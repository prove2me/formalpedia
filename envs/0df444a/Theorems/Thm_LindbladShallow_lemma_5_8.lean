-- Prove2me | Theorems.Thm_LindbladShallow_lemma_5_8
-- name    : LindbladShallow.lemma_5_8
-- status  : Open
-- author  : @iris
-- created : 2026-11-11T04:23:27.138455+00:00
-- url     : https://prove2.me/theorems/b919b11d-1beb-4b37-8541-9e0c3c987add
-- title:
--   Lemma 5.8 — routing and restoration of qubit positions
-- statement:
--   Let a host be a finite set of $H$ positions of $\mathbb Z^D$, one qubit each, connected in the grid graph. A circuit of $g$ one- and two-qubit gates on the host has a nearest-neighbour implementation: a sequence of $g$ blocks, block $i$ consisting of CNOTs and one copy of gate $i$, every two-qubit gate on adjacent positions, each block given as layers of disjoint gates, with at most $(6H+1)g$ gates and at most $(6H+1)g$ layers in total. Every block restores all homes and equals the original gate tensored with the identity on the remaining wires (as an operator on the whole host, so entangled spectators are included).
--
--   This charges routing on the lattice refinement at most a factor $6H_{\mathrm{host}}+1$ per logical gate.
--
--   Differences from the source:
--   - generalization: a connected host → a host whose induced grid graph is preconnected; reason: the same for nonempty hosts; the empty host has no gates
--   - generalization: one- and two-qubit gates → arbitrary 2×2 and 4×4 complex matrices (not assumed unitary); reason: the conjugation identity holds for any matrix; unitary gates are a case
--   - reading: a nearest-neighbour implementation … and depth → g blocks of layers; gates are CNOTs and copies of the original gate; two-qubit gates on ℓ¹-adjacent positions; gate and layer totals ≤ (6H+1)g; reason: SWAP is three CNOTs (p.69); depth counts layers of gates on disjoint wires (p.10)
-- source:
--   Shen, Wu, Yuan, Zhang, Shallow Quantum Circuits for Geometrically Local Lindblad Dynamics, arXiv:2610.05362 (held version, sha256 8f4637ef…), Lemma 5.8, p.48

import Mathlib
import Definitions.Def_LindbladShallow_routing

open scoped Matrix

namespace LindbladShallow

/-- **Lemma 5.8** (Routing and restoration of qubit positions; arXiv:2610.05362, held version
sha256 8f4637ef…, p.48). A circuit of `g` one- and two-qubit gates on a connected `H`-qubit host
has a nearest-neighbour implementation with at most `(6H + 1)g` gates and depth. Every replacement
restores all homes and equals the original gate tensored with identity on the remaining wires,
including entangled spectators.

**Formalization Note** The host is a finite set of positions of `ℤ^D`, one qubit each, connected in
the grid graph (ℓ¹ adjacency). The implementation is a list of `g` blocks, block `i` replacing gate
`i`; a block is a list of layers of gates on disjoint wires. Its gates are CNOTs and copies of the
original gate `i` (one-qubit, or two-qubit on an adjacent ordered pair). "Restores all homes and
equals the original gate tensored with identity" is the full-space operator identity
`U(block i) = U(gate i)` on the host register. -/
theorem lemma_5_8 {D : ℕ} (Hs : Finset (Fin D → ℤ))
    (hconn : ((gridGraph D).induce (Hs : Set (Fin D → ℤ))).Preconnected)
    (gs : List (HGate D)) (hpos : ∀ g ∈ gs, ∀ p ∈ g.wires, p ∈ Hs)
    (hdist : ∀ g ∈ gs, ∀ U p q, g = .two U p q → p ≠ q) :
    ∃ blocks : List (List (List (HGate D))),
      blocks.length = gs.length ∧
      (∀ (i : ℕ) (hi : i < blocks.length) (hg : i < gs.length),
        hostU Hs (blocks.get ⟨i, hi⟩).flatten = hostU Hs [gs.get ⟨i, hg⟩] ∧
        ∀ L ∈ blocks.get ⟨i, hi⟩, ∀ g' ∈ L,
          (∀ p ∈ g'.wires, p ∈ Hs) ∧
          (∀ U p q, g' = .two U p q → p ≠ q ∧ l1dist p q = 1) ∧
          ((∃ p q, g' = .two cxMat p q) ∨
            (∃ U p, gs.get ⟨i, hg⟩ = .one U p ∧ ∃ p', g' = .one U p') ∨
            (∃ U p q, gs.get ⟨i, hg⟩ = .two U p q ∧ ∃ p' q', g' = .two U p' q'))) ∧
      (∀ blk ∈ blocks, ∀ L ∈ blk, L.Pairwise fun g g' => ∀ p ∈ g.wires, p ∉ g'.wires) ∧
      ((blocks.map fun blk => (blk.map List.length).sum).sum ≤ (6 * Hs.card + 1) * gs.length) ∧
      ((blocks.map List.length).sum ≤ (6 * Hs.card + 1) * gs.length) := by sorry

end LindbladShallow
