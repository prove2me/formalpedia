-- Prove2me | Theorems.Thm_GeoQAC_corollary_3_10
-- name    : GeoQAC.corollary_3_10
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T11:32:10.130042+00:00
-- url     : https://prove2.me/theorems/317d0e7f-eca7-4c1b-9684-7601c7fbcde5
-- title:
--   Corollary 3.10 — output variance of a sum of one-qubit contractions
-- statement:
--   Let $|\psi\rangle=C|0^{n+a}\rangle$ be the output of a depth-$d$, width-$w$ 2D-QAC circuit on the grid $[w]\times[h]$. For any sum $A=\sum_{j=1}^n A_j$ of Hermitian single-qubit contractions on distinct target qubits,
--   $$
--   \mathrm{Var}_\psi(A)\le K^d\cdot n\cdot w^{3d+1},
--   $$
--   where $K$ is the constant from Theorem 3.7.
--
--   This is the form in which the potential bound is applied to Boolean functions.
--
--   Differences from the source:
--   - encoding: "$K$ is the constant from Theorem 3.7" → one existential $K\ge2$ for which both Theorem 3.7's bound and the corollary's bound are stated; reason: separate items cannot share an existential constant, and stating both bounds for the same $K$ is the identification.
-- source:
--   Dong, Ou, Yao, On the Computational Power of Geometrically Local QAC circuits, arXiv:2604.07178 (version of 2026-11-03), Corollary 3.10, p.17

import Mathlib
import Definitions.Def_ObliviousRSP_pureState
import Definitions.Def_GeoQAC_QACCircuit_Is2D
import Definitions.Def_GeoQAC_lmv

namespace GeoQAC

open ObliviousRSP (pureState)

open Matrix
open scoped Matrix.Norms.L2Operator

/-- **Corollary 3.10** (arXiv:2604.07178, version of 2026-11-03, p.17). Let `|ψ⟩ = C|0^{n+a}⟩` be the
output of a depth-`d`, width-`w` 2D-QAC circuit. For any sum `A = ∑_{j=1}^n A_j` of Hermitian
single-qubit contractions on distinct target qubits, `Var_ψ(A) ≤ K^d · n · w^{3d+1}`, where `K` is the
constant from Theorem 3.7.

**Formalization Note.** "The constant from Theorem 3.7" is encoded by stating Theorem 3.7's bound for
the same `K` in the first conjunct. The `n` targets are any injective placement `tgt` among the `wh`
qubits, all of which start in `|0⟩`; `A_j` is a `2 × 2` Hermitian matrix of operator norm `≤ 1`
acting on qubit `tgt j`. -/
theorem corollary_3_10 : ∃ K : ℝ, 2 ≤ K ∧
    (∀ (w h d : ℕ) (C : QACCircuit (Pos w h) d), C.Is2D →
      lmv (pureState (C.matrix *ᵥ basisVec (fun _ => false))) ≤ (K * (w : ℝ) ^ 3) ^ d) ∧
    ∀ (w h d n : ℕ) (C : QACCircuit (Pos w h) d) (tgt : Fin n ↪ Pos w h)
      (A : Fin n → Matrix Bool Bool ℂ), C.Is2D → (∀ j, (A j).IsHermitian ∧ ‖A j‖ ≤ 1) →
      var (pureState (C.matrix *ᵥ basisVec (fun _ => false))) (∑ j, embed1 (tgt j) (A j)) ≤
        K ^ d * (n : ℝ) * (w : ℝ) ^ (3 * d + 1) := by sorry

end GeoQAC
