-- Prove2me | Theorems.Thm_MixFlex_RiskNeutral_correlation_eq_one_affine
-- name    : MixFlex.RiskNeutral.correlation_eq_one_affine
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T21:57:45.439736+00:00
-- url     : https://prove2.me/theorems/a519e42f-a645-489d-a5d5-9daa475ecd70
-- title:
--   Proof of PROPOSITION 1(iii) — correlation one means positive affine dependence
-- statement:
--   Let $U,V$ be square-integrable random variables on a probability space with $\operatorname{Var}U>0$ and $\operatorname{Var}V>0$, and suppose their correlation coefficient is
--   $$
--   \rho(U,V)=\frac{\operatorname{Cov}(U,V)}{\sqrt{\operatorname{Var}U\,\operatorname{Var}V}}=1.
--   $$
--   Then there are constants $a>0$ and $b$ with $V=aU+b$ almost surely.
--
--   In the proof of Proposition 1(iii) this is applied to $\rho_{1n}=1$ to write $\tilde X_n=a_{1n}\tilde X_1+b_{1n}$ with $a_{1n}>0$ for $n=2,\dots,N$.
--
--   **Formalization Note** Square integrability and positive variances are the conditions under which the correlation coefficient is defined.
-- source:
--   Tomlin and Wang, On the value of mix flexibility and dual sourcing in unreliable newsvendor networks, Manufacturing Service Oper. Management 7(1), 2005, p. 52, Appendix A, proof of PROPOSITION 1(iii)

import Mathlib
import Definitions.Def_MixFlex_RiskNeutral_Model

namespace MixFlex.RiskNeutral

open MeasureTheory ProbabilityTheory

/-- Proof of Proposition 1(iii), p. 52: two square-integrable random variables with positive
variances and correlation coefficient `1` are almost surely related by `V = a U + b` with `a > 0`. -/
theorem correlation_eq_one_affine {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (U V : Ω → ℝ) (hU : MemLp U 2 μ) (hV : MemLp V 2 μ)
    (hvarU : 0 < variance U μ) (hvarV : 0 < variance V μ) (hρ : correlation μ U V = 1) :
    ∃ a b : ℝ, 0 < a ∧ V =ᵐ[μ] fun ω => a * U ω + b := by sorry

end MixFlex.RiskNeutral
