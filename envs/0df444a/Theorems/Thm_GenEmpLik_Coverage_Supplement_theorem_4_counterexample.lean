-- Prove2me | Theorems.Thm_GenEmpLik_Coverage_Supplement_theorem_4_counterexample
-- name    : GenEmpLik.Coverage.Supplement.theorem_4_counterexample
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T23:20:37.14765+00:00
-- url     : https://prove2.me/theorems/34e02aff-aeab-47d2-a01f-1f89970bacef
-- title:
--   Theorem 4 (corrected: counterexample to the printed one-sided coverage limits)
-- statement:
--   The one-sided coverage limits of Theorem 4 are false as printed when the optimal loss has variance zero. Take iid Rademacher observations $\xi_i$, $X=[-1,1]$, $\ell(x;\xi)=x^2+x\xi$, $f(t)=(t-1)^2$ and $\rho=1$. All hypotheses of Theorem 4 hold: $f$ satisfies Assumption A; $X$ is compact and $\ell(\cdot;\xi)$ is $3$-Lipschitz (Assumption B, with $E M^2=9<\infty$); the extended sample losses are proper and lower semicontinuous (Assumption C); and $E|\ell(x_0;\xi)|^2<\infty$. The population solution set is the singleton $S^\star_{P_0}=\{0\}$ and $\operatorname{Var}\ell(0;\xi)=0$.
--
--   With $T_{\rm opt}(P)=\inf_{x\in X}E_P\ell(x;\xi)$, $u_n=\sup\{T_{\rm opt}(P):D_f(P\|\widehat P_n)\le 1/n\}$ and $l_n$ the corresponding infimum,
--   $$\lim_{n\to\infty}P\big(T_{\rm opt}(P_0)\le u_n\big)=P(\chi^2_1\le1),\qquad \lim_{n\to\infty}P\big(T_{\rm opt}(P_0)\ge l_n\big)=1,$$
--   and
--   $$P(\chi^2_1\le1)<1-\tfrac12P(\chi^2_1\ge1)<1 .$$
--   Theorem 4 asserts that, for a singleton solution set, both limits equal $1-\tfrac12P(\chi^2_1\ge\rho)$; neither does. Its first general limit $P(\inf_{S^\star}H_+\ge0)$ also fails, since here $H_+(0)=G(0)=0$ almost surely and that probability is $1$. The item asserts the source hypotheses together with the actual limits, so the refutation does not rest on a vacuous or missing hypothesis.
--
--   **Formalization Note** $u_n$ and $l_n$ are the real `sSup` and `sInf` of the published optimal-value confidence image; for $n\ge1$ that image is nonempty (it contains the uniform weights) and lies in $[-1/4,0]$, so neither is a default value. The proof in Appendix C.3 obtains weak convergence of $\sqrt n(u_n-T_{\rm opt}(P_0))$ to $\inf_{S^\star}H_+$ and calls it equivalent to the probability limit; that step needs the limit law to have no atom at $0$, which fails when the optimal loss is degenerate. DISPROOF.md gives the calculation. The lower general clause $P(\inf_{S^\star}H_-\le0)$ is not refuted by this model (both sides equal $1$) and is not stated separately.
--
--   Differences from the source:
--   - correction: one-sided coverage limits P(inf H+ ≥ 0), P(inf H- ≤ 0) and the singleton value 1 - P(chi-square_1 ≥ rho)/2 under Assumptions A, B, C → a Rademacher quadratic-loss counterexample satisfying every printed premise, with limits P(chi-square_1 ≤ 1) and 1 at rho = 1; reason: a zero-variance optimal loss gives the limit law an atom at 0, and the weak-convergence step on p. 40 does not yield the probability limit (DISPROOF.md)
--   - encoding: u_n and l_n of (4) for Topt → sSup and sInf of the published optimal-value confidence image; reason: the image is nonempty and bounded for n ≥ 1, so these are the genuine extrema
--   - reading: distributions with divergence at most rho/n from the empirical law → sample-indexed probability weights in the published divergence ball; reason: (4a), (15) and (31) specify absolute continuity
-- source:
--   Duchi, Glynn & Namkoong, Statistics of Robust Optimization: A Generalized Empirical Likelihood Approach, arXiv:1610.03425v3, p. 9, Theorem 4; proof p. 40 (Appendix C.3); counterexample in DISPROOF.md

import Mathlib
import Definitions.Def_GenEmpLik_Coverage_AssumptionA
import Definitions.Def_GenEmpLik_Coverage_AssumptionB
import Definitions.Def_GenEmpLik_Coverage_optimalValue
import Definitions.Def_GenEmpLik_Coverage_confidenceSet
import Definitions.Def_GenEmpLik_Consistency_argminSet
import Definitions.Def_GenEmpLik_Coverage_Supplement_AssumptionC
import Definitions.Def_GenEmpLik_Coverage_Supplement_coverageCounterexample
import Definitions.Def_GenEmpLik_Coverage_Supplement_theorem4Counterexample

open MeasureTheory ProbabilityTheory Filter
open scoped Topology ENNReal

namespace GenEmpLik.Coverage.Supplement

/-- Counterexample to Theorem 4 as printed, p. 9. For ℓ(x; ξ) = x² + xξ on X = [-1, 1]
with iid Rademacher data, f(t) = (t - 1)² and ρ = 1, every hypothesis of Theorem 4 holds
and the population solution set is the singleton {0}. The upper bound u_n is the supremum
of T_opt over the empirical divergence ball, and the probability that it covers the
population optimal value tends to P(χ²₁ ≤ 1), while the probability that the lower bound l_n
(the infimum) covers it tends to 1. Both differ from the printed singleton value
1 - P(χ²₁ ≥ 1)/2, which lies strictly between them. -/
theorem theorem_4_counterexample
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ξ : ℕ → Ω → Fin 2)
    (hξmeas : ∀ i, Measurable (ξ i)) (hξindep : iIndepFun ξ μ)
    (hξlaw : ∀ i, μ.map (ξ i) = rademacherLaw) :
    GenEmpLik.Coverage.AssumptionA counterexampleGenerator ∧
    GenEmpLik.Coverage.AssumptionB symmetricUnitInterval degenerateLoss (fun _ => 3) ∧
    AssumptionC symmetricUnitInterval degenerateLoss rademacherLaw ∧
    (∀ x, Measurable (degenerateLoss x)) ∧
    Integrable (fun _ : Fin 2 => (3 : ℝ) ^ 2) rademacherLaw ∧
    (∃ x0 ∈ symmetricUnitInterval,
      Integrable (fun z => degenerateLoss x0 z ^ 2) rademacherLaw) ∧
    GenEmpLik.Consistency.argminSet symmetricUnitInterval
      (fun x => ∫ z, degenerateLoss x z ∂rademacherLaw) = {0} ∧
    variance (degenerateLoss 0) rademacherLaw = 0 ∧
    Tendsto (fun n : ℕ => μ {ω |
      GenEmpLik.Coverage.optimalValue symmetricUnitInterval degenerateLoss rademacherLaw ≤
        sSup (GenEmpLik.Coverage.confidenceSet symmetricUnitInterval degenerateLoss
          counterexampleGenerator 1 (fun i : Fin n => ξ i ω))}) atTop
      (𝓝 (gaussianReal 0 1 {x : ℝ | x ^ 2 ≤ 1})) ∧
    Tendsto (fun n : ℕ => μ {ω |
      sInf (GenEmpLik.Coverage.confidenceSet symmetricUnitInterval degenerateLoss
          counterexampleGenerator 1 (fun i : Fin n => ξ i ω)) ≤
        GenEmpLik.Coverage.optimalValue symmetricUnitInterval degenerateLoss rademacherLaw})
      atTop (𝓝 1) ∧
    gaussianReal 0 1 {x : ℝ | x ^ 2 ≤ 1} <
      1 - (1 / 2 : ℝ≥0∞) * gaussianReal 0 1 {x : ℝ | 1 ≤ x ^ 2} ∧
    1 - (1 / 2 : ℝ≥0∞) * gaussianReal 0 1 {x : ℝ | 1 ≤ x ^ 2} < 1 := by sorry

end GenEmpLik.Coverage.Supplement
