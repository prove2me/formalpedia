-- Prove2me | Theorems.Thm_MemoSDPI_Main_proposition_2_3
-- name    : MemoSDPI.Main.proposition_2_3
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T21:42:38.288327+00:00
-- url     : https://prove2.me/theorems/c6933d55-350c-43e0-9c7a-e2d9696bed7e
-- title:
--   Proposition 2.3 — an η-SDPI between parameter and sample gives mem_n(A, P) ≥ ((1 − η)/η) I(A(S); θ)
-- statement:
--   Let $P = (P_\theta)_{\theta\sim\Psi}$ be an average-case problem: a prior $\Psi$ on a parameter space $\Theta$ and a measurable family of data distributions $P_\theta$ on $X$; draw $\theta\sim\Psi$ and then $S = (X_1,\dots,X_n)$ with records independent from $P_\theta$. Let $A$ be an algorithm with output space $Y$ whose seed is independent of $(\theta,S)$, and $U = A(S)$.
--   If $(\theta, S)$ satisfies an $\eta$-SDPI for some $0 < \eta < 1$, then every algorithm $A$ satisfies
--   $$
--   \mathrm{mem}_n(A, P) \;\ge\; \frac{1-\eta}{\eta}\, I(A(S); \theta).
--   $$
--   This is the mechanism of all the memorization lower bounds of the paper: an accurate output must carry information about $\theta$, and the SDPI forces it to carry proportionally more about the sample.
--
--   **Formalization Note** Both sides are in $[0,\infty]$; the factor $(1-\eta)/\eta$ enters through `ENNReal.ofReal`. The family $\theta\mapsto P_\theta$ is assumed measurable. The algorithm's output space $Y$ is arbitrary.
--
--   Differences from the source:
--   - encoding: an average-case problem (P_θ) with θ ∼ Ψ → Ψ a probability measure and Measurable P with each P θ a probability measure; reason: drawing S given θ presupposes a measurable family
--   - encoding: ((1 − η)/η) I(A(S); θ) as a real multiple → ENNReal.ofReal ((1 − η)/η) * I in ℝ≥0∞; reason: informations take values in [0, ∞]; (1 − η)/η > 0
-- source:
--   Feldman, Lyu, Talwar, Lower Bounds for Memorization, Privacy and Replicability from Not-So-Strong Data Processing Inequalities, STOC 2027 submission (manuscript sha256 dbb300da…), p. 10, Proposition 2.3

import Mathlib
import Definitions.Def_DPVerify_RandAlg
import Definitions.Def_ThompsonTutorial_InfoRatio_mutualInfo
import Definitions.Def_MemoSDPI_Main_SDPI
import Definitions.Def_MemoSDPI_Main_Memorization

set_option autoImplicit false

open MeasureTheory ProbabilityTheory

namespace MemoSDPI.Main

/-- Feldman, Lyu, Talwar, *Lower Bounds for Memorization, Privacy and Replicability from Not-So-Strong Data Processing Inequalities*, STOC 2027 submission (manuscript sha256 dbb300da…), p. 10, Proposition 2.3: if `(θ, S)` satisfies an `η`-SDPI for some `0 < η < 1`, then
every algorithm `A` satisfies `mem_n(A, P) ≥ ((1 − η)/η) · I(A(S); θ)`. -/
theorem proposition_2_3 {Θ X : Type} [MeasurableSpace Θ] [MeasurableSpace X] {n : ℕ}
    (Ψ : Measure Θ) [IsProbabilityMeasure Ψ] (P : Θ → Measure X)
    [∀ θ, IsProbabilityMeasure (P θ)] (hP : Measurable P)
    (η : ℝ) (hη0 : 0 < η) (hη1 : η < 1) (hSDPI : SatisfiesSDPI (paramSampleLaw Ψ P n) η)
    {Y : Type} [MeasurableSpace Y] (A : DPVerify.RandAlg X Y n) :
    ENNReal.ofReal ((1 - η) / η) * infoParam A Ψ P ≤ memAvg A Ψ P := by sorry

end MemoSDPI.Main
