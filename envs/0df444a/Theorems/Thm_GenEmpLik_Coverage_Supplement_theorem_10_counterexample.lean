-- Prove2me | Theorems.Thm_GenEmpLik_Coverage_Supplement_theorem_10_counterexample
-- name    : GenEmpLik.Coverage.Supplement.theorem_10_counterexample
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T23:19:24.338805+00:00
-- url     : https://prove2.me/theorems/2ef39694-1e7e-49f4-9825-98c9a2bda610
-- title:
--   Theorem 10 (corrected: counterexample to the printed coverage claim)
-- statement:
--   The general functional coverage claim in Theorem 10 is false without further hypotheses. Take $P_0$ uniform on $\{-1,0,1\}$, $H=\{z,z^2\}$, $f(t)=(t-1)^2$ and $\rho=1$. For the moment coordinates $a=E_Pz$ and $b=E_Pz^2$, set $T(a,b)=(b-2/3)^2$ when $a=0$ and $T(a,b)=a$ otherwise. For every iid sample with law $P_0$, all of the printed assumptions hold: $H$ is Donsker with absolute envelope one; $T$ is Hadamard differentiable at $P_0$ on the full signed-measure domain; its whole-space continuous linear derivative is the first coordinate; and its centered influence $z$ has variance $2/3>0$.
--
--   Nevertheless, the actual image coverage satisfies
--   $$\lim_{n\to\infty}P^*\!\left(T(P_0)\in\{T(P):P\ll\widehat P_n,\ D_f(P\|\widehat P_n)\le1/n\}\right)
--   =1-e^{-1/2}=P(\chi_2^2\le1)<P(\chi_1^2\le1).$$
--   The theorem item asserts the source hypotheses as well as the different limiting coverage and strict inequality, so the counterexample does not depend on a vacuous or missing hypothesis. It fulfills this required milestone by refuting the printed universal claim, rather than substituting a restricted positive-variance or finite-class version of it.
--
--   **Formalization Note** The tangent set is the full signed-measure domain, not a thin support of the Gaussian limit. Differentiability at $P_0$ does not guarantee that the confidence image is an interval: here $T(P)=0$ forces both moments to match. DISPROOF.md gives the exact source anchors, differentiability estimate, coverage computation and an investigated continuity repair; no unverified repaired general theorem is proposed.
--
--   Differences from the source:
--   - correction: universal chi-square_1 coverage under the printed tangent differentiability assumptions → a three-atom counterexample satisfying every printed premise with chi-square_2 coverage at radius one; reason: the actual functional image can have a hole despite differentiability at P0; the step on p. 37 from endpoints to actual membership fails (DISPROOF.md)
--   - encoding: the two-degree chi-square probability at one → ENNReal.ofReal of 1 minus exp of negative one half; reason: this is the exact closed form for the chi-square_2 distribution function at one
--   - reading: Pn in (26) → the empirical law P-hat_n; reason: Definition 3 and the proof on p. 37 fix the missing hat
-- source:
--   Duchi, Glynn & Namkoong, Statistics of Robust Optimization: A Generalized Empirical Likelihood Approach, arXiv:1610.03425v3, p. 23, Theorem 10; p. 37 final image-membership inference; counterexample in DISPROOF.md

import Mathlib
import Definitions.Def_GenEmpLik_Coverage_AssumptionA
import Definitions.Def_GenEmpLik_Coverage_Supplement_DonskerClass
import Definitions.Def_GenEmpLik_Coverage_Supplement_Hadamard
import Definitions.Def_GenEmpLik_Coverage_Supplement_influenceFunction
import Definitions.Def_GenEmpLik_Coverage_Supplement_coverageCounterexample

open MeasureTheory ProbabilityTheory Filter
open scoped Topology

namespace GenEmpLik.Coverage.Supplement

/-- Counterexample to Theorem 10 as printed, p. 23. Every source hypothesis
is satisfied on the full probability domain of a three-atom population.
At radius rho=1 the zero fibre fixes two independent moments, so coverage
has the chi-square_2 limit, strictly below the claimed chi-square_1 limit. -/
theorem theorem_10_counterexample
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ξ : ℕ → Ω → Fin 3)
    (hξmeas : ∀ i, Measurable (ξ i)) (hξindep : iIndepFun ξ μ)
    (hξlaw : ∀ i, μ.map (ξ i) = counterexampleLaw) :
    GenEmpLik.Coverage.AssumptionA counterexampleGenerator ∧
    (∃ Γ : Measure (ProcessSpace (Fin 2)),
      IsDonskerWith μ counterexampleLaw ξ counterexampleClass Γ ∧
      Γ (signedDomain counterexampleClass)ᶜ = 0) ∧
    (Measurable (fun _ : Fin 3 => (1 : ℝ)) ∧
      Integrable (fun _ : Fin 3 => (1 : ℝ) ^ 2) counterexampleLaw ∧
      ∀ i j, |counterexampleClass i j| ≤ 1) ∧
    HadamardAt (signedDomain counterexampleClass) (probabilityDomain counterexampleClass)
      (signedDomain counterexampleClass) counterexampleFunctional
      (measureProcess counterexampleClass counterexampleLaw) counterexampleDerivative ∧
    IsInfluence counterexampleClass counterexampleLaw counterexampleDerivative
      (counterexampleClass 0) ∧
    0 < variance (counterexampleClass 0) counterexampleLaw ∧
    Tendsto (fun n : ℕ => μ {ω |
      counterexampleFunctional (measureProcess counterexampleClass counterexampleLaw) ∈
        functionalImage counterexampleClass counterexampleFunctional counterexampleGenerator 1
          (fun i : Fin n => ξ i ω)}) atTop
      (𝓝 (ENNReal.ofReal (1 - Real.exp (-(1 : ℝ) / 2)))) ∧
    ENNReal.ofReal (1 - Real.exp (-(1 : ℝ) / 2)) <
      (gaussianReal 0 1) {x : ℝ | x ^ 2 ≤ 1} := by sorry

end GenEmpLik.Coverage.Supplement
