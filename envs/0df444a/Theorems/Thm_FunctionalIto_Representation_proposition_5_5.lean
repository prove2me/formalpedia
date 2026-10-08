-- Prove2me | Theorems.Thm_FunctionalIto_Representation_proposition_5_5
-- name    : FunctionalIto.Representation.proposition_5_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T00:22:12.374763+00:00
-- url     : https://prove2.me/theorems/e4de1f11-7253-4837-832c-b9b67768c0d4
-- title:
--   Proposition 5.5, p. 17 — integration by parts on D(X): E[Y(T)Z(T)] = E∫₀ᵀ ∇_XY ∇_XZ d[X] (51)
-- statement:
--   Under Assumption 5.1 (with $\mathcal F=\mathcal F^X$ and $E[X](T)<\infty$), let $Y,Z\in D(X)=\mathcal C_b^{1,2}(X)\cap\mathcal I^2(X)$, with vertical derivatives $\nabla_XY$, $\nabla_XZ$ obtained from any functional representations. Then $Y(T)Z(T)$ is integrable, $(\nabla_XY)^{\top}A\,\nabla_XZ$ is integrable on $(0,T]\times\Omega$, and
--   $$E[Y(T)Z(T)]=E\left[\int_0^T\nabla_XY(t)\,\nabla_XZ(t)\,d[X](t)\right].\tag{51}$$
--
--   This identity is what allows $\nabla_X$ to be extended from $D(X)$ to a weak derivative on the square-integrable martingales (Theorem 5.8).
--
--   **Formalization Note.** With $d[X]=A\,dt$, the integrand $\nabla_XY\,\nabla_XZ\,d[X]$ is $(\nabla_XY)^{\top}A\,(\nabla_XZ)\,dt$. Integrability of both sides is part of the conclusion, so the identity is not satisfied by the junk value $0$ of a non-integrable Bochner integral.
-- source:
--   Cont and Fournié, Functional Itô calculus and stochastic integral representation of martingales, arXiv:1002.2446v5, p. 17, Proposition 5.5, (51)

import Mathlib
import Definitions.Def_auto_M05_f3f59_EthierKurtz_HasCrossVariation
import Definitions.Def_EthierKurtz_IsStandardBrownian
import Definitions.Def_FunctionalIto_Representation_Setting
import Definitions.Def_FunctionalIto_Representation_L2

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal Topology BigOperators Matrix

namespace FunctionalIto.Representation

theorem proposition_5_5
    {d : ℕ} {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (T : ℝ≥0) (W : ℝ≥0 → Ω → EthierKurtz.SDEState d) (𝒢 ℱ : Filtration ℝ≥0 ‹MeasurableSpace Ω›)
    (σ : ℝ≥0 → Ω → Matrix (Fin d) (Fin d) ℝ) (X : ℝ≥0 → Ω → (Fin d → ℝ))
    (A : ℝ≥0 → Ω → Matrix (Fin d) (Fin d) ℝ) (hS : IsBrownianSetting P T W 𝒢 σ X ℱ A)
    (Y Z : ℝ≥0 → Ω → ℝ) (ψ ζ : ℝ≥0 → Ω → (Fin d → ℝ))
    (hY : IsVertDerivD P ℱ T X A Y ψ) (hZ : IsVertDerivD P ℱ T X A Z ζ) :
    Integrable (fun ω => Y T ω * Z T ω) P ∧ QIntegrable P T A ψ ζ ∧
      ∫ ω, Y T ω * Z T ω ∂P = QInner P T A ψ ζ := by sorry

end FunctionalIto.Representation
