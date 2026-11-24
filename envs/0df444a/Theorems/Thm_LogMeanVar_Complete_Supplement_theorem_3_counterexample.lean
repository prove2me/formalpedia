-- Prove2me | Theorems.Thm_LogMeanVar_Complete_Supplement_theorem_3_counterexample
-- name    : LogMeanVar.Complete.Supplement.theorem_3_counterexample
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T23:01:37.882999+00:00
-- url     : https://prove2.me/theorems/c4151d67-cd72-4cb0-87c7-b5e4520db35f
-- title:
--   Theorem 3 (corrected: counterexample to sufficient integrability assumptions at ρ=0)
-- statement:
--   The displayed hypotheses of Theorem 3 do not guarantee a finite log-return mean–variance criterion. On a probability space carrying independent stock and state Brownian motions, take $\rho=0$, $T=\gamma=\sigma=1$, $X=B^X$, and $\mu=r=e^{x^4}$. All coefficients are continuous, $\theta=0$, and both displayed integrability conditions hold (the cancelled exponential is identically one).
--
--   Policy (14) is zero, is admissible according to the printed squared-exposure condition, and its actual log-return SDE solution is
--
--   $$R_t=\int_0^t e^{(B^X_s)^4}\,ds.$$
--
--   It is finite on each continuous path, but
--
--   $$\mathbb E[R_1]=+\infty,\qquad R_1\notin L^1(P),\qquad R_1\notin L^2(P).$$
--
--   Thus the full conjunction of claims (14)–(19) cannot be a well-defined finite mean–variance theorem under the printed hypotheses. This counterexample does not reject those formulas on a suitably repaired domain. DISPROOF.md records the Gaussian-tail calculation and the cases an added finite-reward assumption would exclude.
--
--   Differences from the source:
--   - correction: the two hypotheses suffice for the full incomplete-market equilibrium theorem (14)–(19) → an explicit ρ=0 model satisfying both hypotheses with a printed-admissible proposed policy whose actual terminal return has infinite expectation; reason: for every s>0, the Gaussian integral of exp((B_s)^4) is infinite; Tonelli gives E[R_1]=+∞, so the criterion is undefined
--   - reading: ρ² times an integral containing θ/ρ, together with the explicit ρ=0 case on p.19 → cancel the outside ρ² before evaluating ρ=0; the exponent in this θ=0 model is −ρ² R_1/4; reason: agrees with the printed expression when ρ≠0 and gives its supported zero-correlation boundary convention
--   - encoding: the expected return can be nonfinite under the stated hypotheses → nonnegative expectation in ℝ≥0∞ and explicit failure of Integrable and MemLp; reason: retains +∞ instead of a default-zero real integral; continuous Brownian versions exhibit a genuine instance
-- source:
--   Dai, Jin, Kou, Xu, A Dynamic Mean-Variance Analysis for Log Returns, SSRN 3437268 (version of Aug 2019), pp. 18–19, Theorem 3, (14)–(19); p. 19, zero-hedging discussion

import Definitions.Def_LogMeanVar_Complete_Supplement_Countermodels

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology
set_option autoImplicit false

namespace LogMeanVar.Complete.Supplement

/-- Dai, Jin, Kou, Xu, A Dynamic Mean-Variance Analysis for Log Returns,
SSRN 3437268 (version of Aug 2019), pp.18–19, Theorem 3 (corrected: counterexample
to sufficiency of the printed hypotheses at ρ=0). See DISPROOF.md for the calculation.
With μ=r=exp(x⁴), σ=γ=T=1 and X=B^X, θ is identically zero. The two hypotheses
hold, using the source-supported cancelled exponent at ρ=0. The policy (14) is
zero and satisfies the printed A_t condition, but its actual SDE return is not
integrable. Its expectation is +∞, not Lean's default-zero real integral.
Formalization Note: all-path continuous Brownian versions are used only to exhibit
a counterexample. The model's coefficients are continuous in both variables.
This statement replaces the whole false conjunction (14)–(19); it does not claim
that the individual formulas fail under sufficient additional hypotheses. -/
theorem theorem_3_counterexample {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (F : Filtration ℝ≥0 mΩ)
    (B W : ℝ≥0 → Ω → ℝ) (hNoise : CorrelatedNoise P F B W 0)
    (hWcont : ∀ ω, Continuous (fun u => W u ω)) :
    growthModel.Standing ∧
    growthModel.AdaptedAlong F (growthState W) ∧
    IsState growthModel P F W (growthState W) ∧
    IsReturn growthModel P F B (growthState W) (fun _ _ _ => 0)
      0 (fun _ => 0) (growthReturn W) ∧
    PrintedAdmissible growthModel P F (growthState W) (growthReturn W) (fun _ _ _ => 0) 0 ∧
    (∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) 1,
      ENNReal.ofReal (((growthModel.μ s (growthState W s ω) -
        growthModel.r s (growthState W s ω)) / growthModel.σ s (growthState W s ω)) ^ 2)
      ∂volume ∂P) = 0 ∧
    Integrable (growthExponential W 0) P ∧
    (∫⁻ ω, ENNReal.ofReal (growthExponential W 0 ω) ∂P) = 1 ∧
    (∀ s ∈ Set.Ioc (0 : ℝ) 1,
      (∫⁻ ω, ENNReal.ofReal (Real.exp (W s.toNNReal ω ^ 4)) ∂P) = ⊤) ∧
    (∫⁻ ω, ENNReal.ofReal (growthReturn W 1 ω) ∂P) = ⊤ ∧
    ¬Integrable (growthReturn W 1) P ∧ ¬MemLp (growthReturn W 1) 2 P := by sorry

end LogMeanVar.Complete.Supplement
