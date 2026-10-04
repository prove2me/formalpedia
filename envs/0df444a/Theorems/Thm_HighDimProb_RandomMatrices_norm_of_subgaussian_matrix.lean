-- Prove2me | Theorems.Thm_HighDimProb_RandomMatrices_norm_of_subgaussian_matrix
-- name    : HighDimProb.RandomMatrices.norm_of_subgaussian_matrix
-- status  : Disproved
-- author  : @mikedeng1
-- created : 2026-09-19T21:25:22.116892+00:00
-- url     : https://prove2.me/theorems/18e7bb70-96d1-49bb-b0ad-ad1263b5f48a
-- title:
--   Theorem 4.4.5 — Norm of matrices with sub-gaussian entries
-- statement:
--   This is **Theorem 4.4.5**, the goal theorem of this mission: the first non-asymptotic bound
--   on the operator norm of a random matrix, obtained by the ε-net argument this mission's other
--   items assemble (Corollary 4.2.13 supplies small nets of the unit spheres; Exercise 4.4.3(a)
--   reduces the operator norm to a supremum over those nets; a union bound over the finite nets,
--   combined with the sub-gaussian tail of each fixed quadratic form $\langle Ax, y\rangle$,
--   completes the argument).
--
--   There is an absolute constant $C > 0$ such that the following holds. Let $A$ be an
--   $m \times n$ random matrix whose entries $A_{ij}$ are independent, mean-zero, sub-gaussian
--   random variables, and let $K = \max_{i,j} \|A_{ij}\|_{\psi_2}$ (companion definition
--   `HighDimProb.Concentration.subgaussianNorm`, this series' published sub-gaussian norm). Then,
--   for any $t > 0$,
--
--   $$
--   \mathrm{Prob}\bigl\{\, \|A\| \le CK(\sqrt m + \sqrt n + t) \,\bigr\} \;\ge\; 1 - 2\exp(-t^2),
--   $$
--
--   where $\|A\|$ is the operator norm (companion definition `matrixOpNorm`).
--
--   **Formalization Note** $C$ is existentially quantified ahead of every other object (the
--   probability space, $m$, $n$, the matrix $A$, its independence and mean-zero hypotheses, $K$,
--   and $t$), so no numeral is fixed for it, matching the book's own convention that "$C$ and $c$
--   will always denote some positive absolute constants". Independence of the $mn$ entries is
--   `iIndepFun` over the index set $\mathrm{Fin}\ m \times \mathrm{Fin}\ n$; "mean zero" is the
--   Bochner integral of each entry equal to $0$; $t > 0$ is imposed explicitly, matching "for any
--   $t > 0$" rather than a hidden "with high probability".
-- source:
--   Vershynin, High-Dimensional Probability (2018), Theorem 4.4.5, p. 91 (PDF p. 99)

import Mathlib
import Definitions.Def_HighDimProb_Concentration_SubgaussianNorm
import Definitions.Def_HighDimProb_RandomMatrices_matrixOpNorm

open MeasureTheory ProbabilityTheory

namespace HighDimProb.RandomMatrices

/-- **Theorem 4.4.5** (Norm of matrices with sub-gaussian entries), Vershynin,
*High-Dimensional Probability* (2018), p. 91.

Let `A` be an `m × n` random matrix whose entries `Aᵢⱼ` are independent, mean zero,
sub-gaussian random variables. Then, for any `t > 0`, `‖A‖ ≤ CK(√m + √n + t)` with
probability at least `1 − 2exp(−t²)`, where `K = maxᵢ,ⱼ ‖Aᵢⱼ‖ψ2`. -/
theorem norm_of_subgaussian_matrix :
    ∃ C : ℝ, 0 < C ∧
      ∀ {Ω : Type} [MeasurableSpace Ω] (Prob : Measure Ω) [IsProbabilityMeasure Prob]
        {m n : ℕ} (hm : 0 < m) (hn : 0 < n) (A : Ω → Matrix (Fin m) (Fin n) ℝ)
        (hindep : iIndepFun (fun p : Fin m × Fin n => fun ω => A ω p.1 p.2) Prob)
        (hmean : ∀ i j, ∫ ω, A ω i j ∂Prob = 0)
        (K : ℝ) (hK : ∀ i j, HighDimProb.Concentration.subgaussianNorm Prob (fun ω => A ω i j) ≤ K)
        (t : ℝ) (ht : 0 < t),
        1 - 2 * Real.exp (-(t ^ 2)) ≤
          Prob.real {ω | matrixOpNorm (A ω) ≤ C * K * (Real.sqrt m + Real.sqrt n + t)} := by sorry

end HighDimProb.RandomMatrices
