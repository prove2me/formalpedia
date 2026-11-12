-- Prove2me | Theorems.Thm_GenEmpLik_Coverage_expansion_after_37_lower
-- name    : GenEmpLik.Coverage.expansion_after_37_lower
-- status  : Proved
-- author  : @tianyipeng
-- created : 2026-11-07T02:02:53.975163+00:00
-- url     : https://prove2.me/theorems/f79b41e0-3fe9-4933-a23e-9e8250ffde10
-- title:
--   Stochastic expansion of the lower endpoint for the optimal value
-- statement:
--   Assume the hypotheses of Theorem 3: $\mathcal X\subset\mathbb R^d$ is nonempty and compact, the losses are measurable and satisfy Assumption B with $\mathbb E_{P_0}[M^2]<\infty$, $\mathbb E_{P_0}[|\ell(x_0;\xi)|^2]<\infty$ for some $x_0\in\mathcal X$, $f$ satisfies Assumption A, $\xi_1,\xi_2,\dots$ are i.i.d. with law $P_0$, and the population optimizer $x^\star$ is unique with $\operatorname{Var}_{P_0}(\ell(x^\star;\xi))>0$. Let $\rho\ge0$ and $T^{(1)}(\xi;P_0)=\ell(x^\star;\xi)-\mathbb E_{P_0}[\ell(x^\star;\xi)]$ be the influence function of $T_{\rm opt}$. Then
--
--   $$\sqrt n\Big(\inf_{P:\,D_f(P\|\widehat P_n)\le\rho/n}T_{\rm opt}(P)-T_{\rm opt}(P_0)\Big)-\sqrt n\,\mathbb E_{\widehat P_n}\big[T^{(1)}(\xi;P_0)\big]+\sqrt{\rho\operatorname{Var}_{\widehat P_n}\big(T^{(1)}(\xi;P_0)\big)}=o_P(1).$$
--
--   Here the infimum runs over probability weight vectors $p$ on the sample with $\frac1n\sum_i f(np_i)\le\rho/n$, $T_{\rm opt}(p)=\inf_{x\in\mathcal X}\sum_ip_i\ell(x;\xi_i)$, and $\operatorname{Var}_{\widehat P_n}$ is the empirical variance with normalization $1/n$. This is the lower-endpoint counterpart of the expansion displayed after (37). It follows from the same argument applied to $-T$, that is, Theorem 9 for the negated influence function together with Lemma 16. Combined with the central limit theorem, it gives $P(T_{\rm opt}(P_0)\ge\inf_PT_{\rm opt}(P))\to P(N(0,1)\le\sqrt\rho)$.
--
--   **Formalization note.** $o_P(1)$ is stated as: for every $\delta>0$, the (outer) probability that the absolute value of the left-hand side exceeds $\delta$ tends to $0$.
-- source:
--   Duchi, Glynn & Namkoong, Statistics of Robust Optimization: A Generalized Empirical Likelihood Approach, arXiv:1610.03425v3, Appendix B.4 (proof of Theorem 10), p. 37, display after (37) and the sentence 'By an exactly symmetric argument on -T(P0) ...'; specialized to T_opt via Appendix C.1.

import Mathlib
import Definitions.Def_GenEmpLik_Coverage_AssumptionA
import Definitions.Def_GenEmpLik_Coverage_AssumptionB
import Definitions.Def_GenEmpLik_Coverage_optimalValue
import Definitions.Def_GenEmpLik_Coverage_empiricalOptimalValue
import Definitions.Def_GenEmpLik_Coverage_divergenceBall
import Definitions.Def_GenEmpLik_Coverage_confidenceSet
import Definitions.Def_GenEmpLik_Coverage_influence
import Definitions.Def_GenEmpLik_Coverage_remainder
import Definitions.Def_GenEmpLik_Coverage_robustUpper
import Definitions.Def_GenEmpLik_Coverage_uniqueOptimizer
import Definitions.Def_VarianceRegularization_Expansion_empMean
import Definitions.Def_VarianceRegularization_Expansion_empVar

open MeasureTheory ProbabilityTheory Filter Topology

namespace GenEmpLik.Coverage

/-- The lower counterpart of the stochastic expansion in Appendix B.4 after (37), p. 37, for
T_opt, obtained by the symmetric argument on -T (Theorem 9 applied to the negated influence
function, together with Lemma 16). -/
theorem expansion_after_37_lower
    {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ξ : ℕ → Ω → Ξ) (d : ℕ)
    (X : Set (EuclideanSpace ℝ (Fin d)))
    (ℓ : EuclideanSpace ℝ (Fin d) → Ξ → ℝ)
    (M : Ξ → ℝ) (f : ℝ → EReal) (ρ : ℝ)
    (hρ : 0 ≤ ρ) (hA : AssumptionA f)
    (hX : X.Nonempty) (hB : AssumptionB X ℓ M)
    (hℓmeas : ∀ x, Measurable (ℓ x))
    (hM2 : Integrable (fun z => M z ^ 2) (μ.map (ξ 0)))
    (hℓ2 : ∃ x0 ∈ X, Integrable (fun z => ℓ x0 z ^ 2) (μ.map (ξ 0)))
    (hξmeas : ∀ i, Measurable (ξ i))
    (hξindep : iIndepFun ξ μ)
    (hξident : ∀ i, IdentDistrib (ξ i) (ξ 0) μ μ)
    (hunique : HasUniqueOptimizer X ℓ (μ.map (ξ 0)))
    (hvar : 0 < variance (ℓ (uniqueOptimizer X ℓ (μ.map (ξ 0)) hunique))
      (μ.map (ξ 0))) :
    ∀ δ : ℝ, 0 < δ →
      Tendsto (fun n : ℕ => μ {ω |
        δ < |Real.sqrt (n : ℝ) *
            (sInf (empiricalOptimalValue X ℓ (fun i : Fin n => ξ i ω) '' divergenceBall f ρ n) -
              optimalValue X ℓ (μ.map (ξ 0))) -
          Real.sqrt (n : ℝ) *
            VarianceRegularization.Expansion.empMean
              (fun i : Fin n => influence ℓ
                (uniqueOptimizer X ℓ (μ.map (ξ 0)) hunique)
                (μ.map (ξ 0)) (ξ i ω)) +
          Real.sqrt (ρ * VarianceRegularization.Expansion.empVar
              (fun i : Fin n => influence ℓ
                (uniqueOptimizer X ℓ (μ.map (ξ 0)) hunique)
                (μ.map (ξ 0)) (ξ i ω)))|}) atTop (𝓝 0) := by sorry

end GenEmpLik.Coverage
