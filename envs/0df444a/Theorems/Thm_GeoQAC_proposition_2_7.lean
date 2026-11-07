-- Prove2me | Theorems.Thm_GeoQAC_proposition_2_7
-- name    : GeoQAC.proposition_2_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T11:32:34.654465+00:00
-- url     : https://prove2.me/theorems/91a7a673-3cd0-45a4-b7f2-f59600fcc917
-- title:
--   Proposition 2.7, bullets 2 and 3 — compute-to-clean and nekomata-to-parity conversions (bullet 1 not included)
-- statement:
--   Let $d\ge1$. The following conversions hold for depth-$d$ $[w,h]$-2D-QAC circuits:
--
--   1. If a circuit computes a Boolean function $f$ exactly and its output qubit lies on the boundary of the rectangle, it gives a clean implementation of $U_f$ by a depth-$O(d)$ $[w+O(1),h+O(1)]$-2D-QAC circuit.
--   2. If a circuit synthesizes an exact $n$-nekomata whose targets occupy consecutive positions in a boundary column, it gives a clean parity implementation on $n$ controls by a depth-$O(d)$ $[w+O(1),h+O(1)]$-2D-QAC circuit. The new input qubits lie in an adjacent column.
--
--   One absolute constant serves every $O(\cdot)$. These are the second and third bullets of Proposition 2.7; the first bullet (parity–fanout equivalence) is not part of this item.
--
--   **Formalization Note** "The new input qubits lie in an adjacent column" is stated through an embedding of the old rectangle into the new one at offsets $(r_1,c_1)$: all $n$ controls lie in one column adjacent to the image $c_1+c$ of the target column $c$, and control $i$ lies in the row $r_1+r_0+i$ of the image of target $i$.
--
--   Differences from the source:
--   - generalization: in the first conversion the source circuit's ancillas $|0^a\rangle$ → any product ancilla state; reason: p.11 allows ancillas "initialized to product states", and $|0\rangle$ is a special case.
--   - encoding: "lie in an adjacent column" → an embedding offset $(r_1,c_1)$ of the old rectangle into the new one with all controls in one column adjacent to column $c_1+c$; reason: the new circuit is on a new grid, so adjacency is relative to the image of the old target column.
--   - generalization: no row placement of the new inputs → control $i$ lies in row $r_1+r_0+i$, beside the image of target $i$; reason: the proof (p.40) places "the input qubits in a fresh column beside the boundary targets", so that the controlled-Z gates coupling input $j$ to target $j$ "are then disjoint adjacent pairs"; the conclusion only gains a clause.
-- source:
--   Dong, Ou, Yao, On the Computational Power of Geometrically Local QAC circuits, arXiv:2604.07178 (version of 2026-11-03), Proposition 2.7 (bullets 2 and 3), p.12 (restated p.39, proved p.40)

import Mathlib
import Definitions.Def_GeoQAC_QACCircuit_Is2D
import Definitions.Def_GeoQAC_ComputesExactly
import Definitions.Def_GeoQAC_IsCleanImpl
import Definitions.Def_GeoQAC_IsNekomataApprox

namespace GeoQAC

/-- **Proposition 2.7, bullets 2 and 3** (arXiv:2604.07178, version of 2026-11-03, p.12; restated
p.39, proved p.40). Let `d ≥ 1`. The following conversions hold for depth-`d` `[w, h]`-2D-QAC
circuits:
* If a circuit computes a Boolean function `f` exactly and its output qubit lies on the boundary of
  the rectangle, it gives a clean implementation of `U_f` by a depth-`O(d)`
  `[w + O(1), h + O(1)]`-2D-QAC circuit.
* If a circuit synthesizes an exact `n`-nekomata whose targets occupy consecutive positions in a
  boundary column, it gives a clean parity implementation on `n` controls by a depth-`O(d)`
  `[w + O(1), h + O(1)]`-2D-QAC circuit. The new input qubits lie in an adjacent column.

**Formalization Note.**
* One absolute constant `K` serves every `O(·)`.
* "Clean implementation" is the exact clean implementation of Definition 2.5 (`IsCleanImpl`,
  ancillas `|0⟩`, one global phase). In bullet 2 the source circuit may start from any product
  ancilla state (p.11), its inputs at any placement.
* Bullet 3: "consecutive positions in a boundary column" is: target `i` at `(r₀ + i, c)`, `c` a
  boundary column. "The new input qubits lie in an adjacent column": the old rectangle sits in the new
  one at offsets `(r₁, c₁)`, all controls lie in one column `c'` adjacent to the image `c₁ + c` of
  the target column, and control `i` sits in the row `r₁ + r₀ + i` of the image of target `i` (the
  proof, p.40: "Place the input qubits in a fresh column beside the boundary targets. The
  controlled-Z gates are then disjoint adjacent pairs").
* Bullet 1 (parity ↔ fanout) is not formalized here. -/
theorem proposition_2_7 : ∃ K : ℕ,
    (∀ (n w h d : ℕ) (C : QACCircuit (Pos w h) d) (inp : Fin n ↪ Pos w h)
      (anc : Pos w h → Bool → ℂ) (out : Pos w h) (f : (Fin n → Bool) → Bool),
      1 ≤ d → C.Is2D → ComputesExactly C inp anc out f → IsBoundary out →
      ∃ (w' h' D : ℕ) (C' : QACCircuit (Pos w' h') D) (ctrl : Fin n ↪ Pos w' h')
        (acc : Pos w' h'),
        C'.Is2D ∧ w' ≤ w + K ∧ h' ≤ h + K ∧ D ≤ K * d ∧ IsCleanImpl C' ctrl acc f) ∧
    (∀ (n w h d : ℕ) (C : QACCircuit (Pos w h) d) (tgt : Fin n ↪ Pos w h) (c : Fin h) (r₀ : ℕ),
      1 ≤ d → C.Is2D → IsBoundaryCol c → (∀ i, (tgt i).2 = c ∧ (tgt i).1.val = r₀ + i.val) →
      IsNekomataApprox 1 C tgt →
      ∃ (w' h' D : ℕ) (C' : QACCircuit (Pos w' h') D) (ctrl : Fin n ↪ Pos w' h')
        (acc : Pos w' h') (r₁ c₁ : ℕ) (c' : Fin h'),
        C'.Is2D ∧ w' ≤ w + K ∧ h' ≤ h + K ∧ D ≤ K * d ∧ IsCleanParity C' ctrl acc ∧
        r₁ + w ≤ w' ∧ c₁ + h ≤ h' ∧
        (c'.val = c₁ + c.val + 1 ∨ c'.val + 1 = c₁ + c.val) ∧
        ∀ i, (ctrl i).2 = c' ∧ (ctrl i).1.val = r₁ + r₀ + i.val) := by sorry

end GeoQAC
