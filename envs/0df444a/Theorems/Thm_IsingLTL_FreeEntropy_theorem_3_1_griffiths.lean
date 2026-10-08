-- Prove2me | Theorems.Thm_IsingLTL_FreeEntropy_theorem_3_1_griffiths
-- name    : IsingLTL.FreeEntropy.theorem_3_1_griffiths
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T00:11:12.657352+00:00
-- url     : https://prove2.me/theorems/faec1598-f116-479e-9a50-309f3ab512c5
-- title:
--   Theorem 3.1 — Griffiths inequality
-- statement:
--   Consider two Ising models $\mu$ and $\mu'$ on graphs $G=(V,E)$ and $G'=(V,E')$ on the same finite vertex set, with inverse temperatures $\beta$, $\beta'$ and magnetic fields $\{B_i\}$, $\{B'_i\}$. If $E\subseteq E'$, $0\le\beta\le\beta'$ and $0\le B_i\le B'_i$ for all $i\in V$, then for every $U\subseteq V$
--   $$0\le\Big\langle\mu,\prod_{i\in U}x_i\Big\rangle\le\Big\langle\mu',\prod_{i\in U}x_i\Big\rangle.$$
--
--   Griffiths' inequality is the monotonicity tool behind every comparison of boundary conditions and fields in the paper.
--
--   **Formalization Note** The hypothesis $\beta\ge0$ is the paper's standing assumption (ferromagnetic model, p. 1), not repeated in the theorem's sentence. The models have no pinned vertices.
-- source:
--   Dembo & Montanari, Ising Models on Locally Tree-Like Graphs, arXiv:0804.4726v3, p. 9, Theorem 3.1 (cited from Liggett, Theorem IV.1.21)

import Mathlib
import Definitions.Def_IsingLTL_FreeEntropy_IsingModel

namespace IsingLTL.FreeEntropy

/-- **Theorem 3.1 (Griffiths inequality)** (Dembo–Montanari, *Ising Models on Locally Tree-Like
Graphs*, arXiv:0804.4726v3, p. 9). Consider two Ising models `μ` and `μ′` on graphs `G = (V, E)`
and `G′ = (V, E′)`, inverse temperatures `β`, `β′` and fields `{B_i}`, `{B′_i}`. If `E ⊆ E′`,
`β ≤ β′` and `0 ≤ B_i ≤ B′_i` for all `i`, then `0 ≤ ⟨μ, ∏_{i∈U} x_i⟩ ≤ ⟨μ′, ∏_{i∈U} x_i⟩` for
every `U ⊆ V`.

Formalization Note: `V` is finite, `E ⊆ E′` is `G ≤ G′`, and the models are the Ising measures
(3.1) on the whole vertex set without pins. The hypothesis `0 ≤ β` is the paper's standing
assumption (ferromagnetic model, p. 1); it is not repeated in the theorem's sentence. -/
theorem theorem_3_1_griffiths {V : Type*} [Fintype V] [DecidableEq V]
    (G G' : SimpleGraph V) [DecidableRel G.Adj] [DecidableRel G'.Adj]
    (β β' : ℝ) (B B' : V → ℝ) (hβ : 0 ≤ β) (hGG' : G ≤ G') (hββ' : β ≤ β')
    (hB : ∀ i, 0 ≤ B i) (hBB' : ∀ i, B i ≤ B' i) (U : Finset V) :
    0 ≤ pairing (isingOn G β B ∅ Finset.univ) (fun x => ∏ i ∈ U, spinOf Finset.univ x i) ∧
      pairing (isingOn G β B ∅ Finset.univ) (fun x => ∏ i ∈ U, spinOf Finset.univ x i) ≤
        pairing (isingOn G' β' B' ∅ Finset.univ) (fun x => ∏ i ∈ U, spinOf Finset.univ x i) := by sorry

end IsingLTL.FreeEntropy
