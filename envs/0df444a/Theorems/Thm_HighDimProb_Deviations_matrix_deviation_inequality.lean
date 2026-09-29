-- Prove2me | Theorems.Thm_HighDimProb_Deviations_matrix_deviation_inequality
-- name    : HighDimProb.Deviations.matrix_deviation_inequality
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-19T23:08:45.902692+00:00
-- url     : https://prove2.me/theorems/8b697fbc-a6e9-49f2-925f-f614a571bc05
-- title:
--   Theorem 9.1.1 — Matrix deviation inequality
-- statement:
--   This is the **matrix deviation inequality**, "the main result of this chapter": a uniform
--   bound, over an arbitrary subset $T\subseteq\mathbb R^n$, on how far $\|Ax\|_2$ can deviate from
--   its typical size $\sqrt m\|x\|_2$, for a random matrix $A$ with independent, isotropic,
--   sub-gaussian rows.
--
--   Let $A$ be an $m\times n$ matrix whose rows $A_1,\dots,A_m$ are independent, isotropic
--   sub-gaussian random vectors in $\mathbb R^n$, with $K := \max_i\|A_i\|_{\psi_2}$. Then for any
--   $T\subseteq\mathbb R^n$,
--   $$
--   \mathbb E\sup_{x\in T}\bigl|\,\|Ax\|_2 - \sqrt m\|x\|_2\,\bigr| \;\le\; CK^2\gamma(T),
--   $$
--   where $\gamma(T)$ is the Gaussian complexity of $T$ (`GaussianComplexity`) and $C$ is an
--   absolute constant.
--
--   **Formalization Note** $A$ is represented by its rows, `A : Fin m → Ω → EuclideanSpace ℝ (Fin
--   n)`; $\|Ax\|_2$ is recovered as $\sqrt{\sum_i\langle A_i,x\rangle^2}$, the Euclidean norm of
--   $(\langle A_1,x\rangle,\dots,\langle A_m,x\rangle) = Ax$. Isotropy and the sub-gaussian bound
--   reuse `IsIsotropic` and `SubgaussianVectorNorm`. The right-hand side presupposes $\gamma(T)$ is
--   a finite real number; since `GaussianComplexity` is `EReal`-valued in general, an explicit real
--   witness $\gamma$ with `GaussianComplexity T = (γ : EReal)` is added (the same finiteness
--   pattern `07-chaining`'s Dudley inequality uses for its own right-hand integral). $E\sup$ on the
--   left is `ExpSup`. $C$ is existentially quantified before every type, instance and hypothesis it
--   is uniform over.
-- source:
--   Vershynin, High-Dimensional Probability (2018), p. 229, Theorem 9.1.1

import Mathlib
import Definitions.Def_HighDimProb_Deviations_ExpSup
import Definitions.Def_HighDimProb_Deviations_IsIsotropic
import Definitions.Def_HighDimProb_Deviations_SubgaussianVectorNorm
import Definitions.Def_HighDimProb_Deviations_GaussianComplexity

open MeasureTheory ProbabilityTheory

namespace HighDimProb.Deviations

/-- **Theorem 9.1.1** (Matrix deviation inequality), Vershynin, *High-Dimensional Probability*
(2018), p. 229 (PDF p. 237).

"Let `A` be an `m × n` matrix whose rows `Aᵢ` are independent, isotropic and sub-gaussian random
vectors in `ℝⁿ`. Then for any subset `T ⊂ ℝⁿ`, we have `E sup_{x∈T} |‖Ax‖₂ − √m‖x‖₂| ≤ CK²γ(T)`.
Here `γ(T)` is the Gaussian complexity introduced in Section 7.6.2, and `K = maxᵢ‖Aᵢ‖_{ψ2}`."

`A` is represented by its rows `A : Fin m → Ω → EuclideanSpace ℝ (Fin n)` (independent per-row
random vectors), matching the book's own row-by-row hypotheses directly; `‖Ax‖₂` is recovered as
`Real.sqrt (∑ i, ⟨Aᵢ,x⟩²)`, the Euclidean norm of the vector `(⟨A₁,x⟩,…,⟨Aₘ,x⟩) = Ax`. `Isotropic`
is `IsIsotropic`(reused, Definition 3.2.1 via its Lemma 3.2.3 characterization) and the norm
bound `K = maxᵢ‖Aᵢ‖_{ψ2}` is stated as `∀ i, subgaussianVectorNorm P (A i) ≤ K` (reused,
Definition 3.4.1), matching the book's `K := maxᵢ‖Aᵢ‖_{ψ2}` without pinning `K` to the literal
max (any upper bound is what the book's own proof, via the `K` appearing only as an upper bound
on each row's norm, actually uses).

The right-hand side `CK²γ(T)` presupposes `γ(T)` is a finite, well-defined real number multiplying
`CK²` — the book's own statement does not spell this out, since `γ(T)` is finite whenever `T` is
bounded (as in every application in the chapter) but `gaussianComplexity` is `EReal`-valued in
general. This is made explicit via `(γ : ℝ)` and `hγ : gaussianComplexity T = (γ : EReal)`, an
explicit real witness for the Gaussian complexity, exactly as `07-chaining`'s Dudley inequality
makes its own right-hand integral's finiteness explicit rather than silently assumed (same trap,
`reference/FAITHFULNESS_TRAPS.md` #14/finiteness pattern). `E sup` on the left is `expSup`
(finite-marginal convention). The constant `C` is existentially quantified before every type,
instance and hypothesis it is uniform over, matching the book's "absolute constant". -/
theorem matrix_deviation_inequality :
    ∃ C : ℝ, 0 < C ∧
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        {m n : ℕ} (A : Fin m → Ω → EuclideanSpace ℝ (Fin n)),
        iIndepFun A P →
        (∀ i, IsIsotropic P (A i)) →
        ∀ (K : ℝ), 0 ≤ K → (∀ i, subgaussianVectorNorm P (A i) ≤ K) →
        ∀ (T : Set (EuclideanSpace ℝ (Fin n))) (γ : ℝ),
          gaussianComplexity T = (γ : EReal) →
          expSup P (fun x : T => fun ω =>
              |Real.sqrt (∑ i, (inner (𝕜 := ℝ) (A i ω) x.1) ^ 2) -
                Real.sqrt m * ‖x.1‖|) ≤
            ((C * K ^ 2 * γ : ℝ) : EReal) := by sorry

end HighDimProb.Deviations
