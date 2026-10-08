-- Prove2me | Theorems.Thm_HighDimProb_Deviations_matrix_deviation_inequality_v2
-- name    : HighDimProb.Deviations.matrix_deviation_inequality_v2
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-10-06T06:19:58.769242+00:00
-- url     : https://prove2.me/theorems/b1106563-6c7e-45fe-9ca3-4e3872a87f6a
-- title:
--   Theorem 9.1.1 — Matrix deviation inequality: $\mathbb E\sup_{x\in T}\bigl|\|Ax\|_2-\sqrt m\|x\|_2\bigr|\le CK^2\gamma(T)$
-- statement:
--   This is the **matrix deviation inequality**, "the main result of this chapter": a uniform bound, over an arbitrary subset $T\subseteq\mathbb R^n$, on how far $\|Ax\|_2$ can deviate from its typical size $\sqrt m\|x\|_2$, for a random matrix $A$ with independent, isotropic, sub-gaussian rows.
--
--   There is an absolute constant $C>0$ such that the following holds. Let $A$ be an $m\times n$ random matrix whose rows $A_1,\dots,A_m$ are independent, isotropic, sub-gaussian random vectors in $\mathbb R^n$ with $\max_i\|A_i\|_{\psi_2}\le K$, where $\|\cdot\|_{\psi_2}$ is the sub-gaussian norm of a random vector (companion definition `subgaussianVectorNorm`, valued in $[0,\infty]$, finite exactly for sub-gaussian random vectors). Then for any $T\subseteq\mathbb R^n$ with Gaussian complexity $\gamma(T)\in\mathbb R$ (`gaussianComplexity`),
--   $$
--   \mathbb E\sup_{x\in T}\bigl|\,\|Ax\|_2-\sqrt m\,\|x\|_2\,\bigr|\;\le\;CK^2\gamma(T).
--   $$
--
--   **Formalization Note.** The retired version was disproved because its real-valued sub-gaussian norm returned the junk value $0$ for a heavy-tailed row, so an isotropic but non-sub-gaussian row satisfied the hypothesis with $K=0$ and the right-hand side collapsed to $0$ while the left-hand side was positive. The new statement uses the corrected `ℝ≥0∞`-valued `subgaussianVectorNorm` (built on the corrected scalar norm) with $K\in[0,\infty)$ (`ℝ≥0`), so $\forall i,\ \|A_i\|_{\psi_2}\le K$ now says that every row *is* a sub-gaussian random vector with norm at most $K$, as the book's "sub-gaussian random vectors … $K=\max_i\|A_i\|_{\psi_2}$" does (any upper bound $K$ is what the proof uses). Everything else is as before: $A$ is represented by its rows, $\|Ax\|_2=\sqrt{\sum_i\langle A_i,x\rangle^2}$; isotropy is `IsIsotropic` (Definition 3.2.1 via Lemma 3.2.3); $\mathbb E\sup$ is `expSup`, the book's finite-marginal convention (footnote 3 to §7.2); since `gaussianComplexity` is `EReal`-valued, $\gamma(T)$ is given by an explicit real witness ($\gamma(T)=+\infty$ makes the book's bound trivial and $T=\emptyset$ is degenerate, so no case of the book is lost); $C$ is existentially quantified before every other object. Edge cases: $m=0$ gives a zero process and $\gamma(T)\ge0$; $n=0$ gives $T\subseteq\{0\}$ and both sides $0$.
-- source:
--   Vershynin, High-Dimensional Probability (CUP 2018), Theorem 9.1.1, p. 229 (PDF p. 237); sub-gaussian random vectors Definition 3.4.1, p. 56; Gaussian complexity Definition 7.6.8, p. 180

import Mathlib
import Definitions.Def_HighDimProb_Deviations_ExpSup
import Definitions.Def_HighDimProb_Deviations_IsIsotropic
import Definitions.Def_HighDimProb_Deviations_SubgaussianVectorNorm_v2
import Definitions.Def_HighDimProb_Deviations_GaussianComplexity

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace HighDimProb.Deviations

/-- **Theorem 9.1.1** (Matrix deviation inequality), Vershynin, *High-Dimensional Probability*
(2018), p. 229 (PDF p. 237).

"Let `A` be an `m × n` matrix whose rows `Aᵢ` are independent, isotropic and sub-gaussian random
vectors in `ℝⁿ`. Then for any subset `T ⊂ ℝⁿ`, we have `E sup_{x∈T} |‖Ax‖₂ − √m‖x‖₂| ≤ CK²γ(T)`.
Here `γ(T)` is the Gaussian complexity introduced in Section 7.6.2, and `K = maxᵢ‖Aᵢ‖_{ψ2}`."

`A` is represented by its rows `A : Fin m → Ω → EuclideanSpace ℝ (Fin n)`; `‖Ax‖₂` is
`Real.sqrt (∑ i, ⟨Aᵢ,x⟩²)`; isotropy is `IsIsotropic` (Definition 3.2.1 via Lemma 3.2.3); `E sup`
is `expSup` (finite-marginal convention, footnote 3 to Section 7.2); `γ(T)` is given by an
explicit real witness `γ` with `gaussianComplexity T = (γ : EReal)` (when `γ(T) = +∞` the
book's bound is trivial, and `T = ∅` is degenerate).

Corrected version (`_v2`): the sub-gaussian bound uses the corrected `ℝ≥0∞`-valued
`subgaussianVectorNorm` (built on the corrected scalar norm, `⊤` for a non-sub-gaussian row) and
`K : ℝ≥0`, so `∀ i, ‖Aᵢ‖_{ψ₂} ≤ K` now states that every row *is* a sub-gaussian random vector
with norm at most `K`, as the book's "sub-gaussian random vectors … `K = maxᵢ‖Aᵢ‖_{ψ2}`" does.
The retired version's real-valued norm returned `0` for a heavy-tailed row, so an isotropic
non-sub-gaussian row satisfied the hypothesis with `K = 0`. -/
theorem matrix_deviation_inequality_v2 :
    ∃ C : ℝ, 0 < C ∧
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        {m n : ℕ} (A : Fin m → Ω → EuclideanSpace ℝ (Fin n)),
        iIndepFun A P →
        (∀ i, IsIsotropic P (A i)) →
        ∀ (K : ℝ≥0), (∀ i, subgaussianVectorNorm P (A i) ≤ K) →
        ∀ (T : Set (EuclideanSpace ℝ (Fin n))) (γ : ℝ),
          gaussianComplexity T = (γ : EReal) →
          expSup P (fun x : T => fun ω =>
              |Real.sqrt (∑ i, (inner (𝕜 := ℝ) (A i ω) x.1) ^ 2) -
                Real.sqrt m * ‖x.1‖|) ≤
            ((C * K ^ 2 * γ : ℝ) : EReal) := by sorry

end HighDimProb.Deviations
