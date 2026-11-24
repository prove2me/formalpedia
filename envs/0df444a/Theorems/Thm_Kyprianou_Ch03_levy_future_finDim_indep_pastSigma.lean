-- Prove2me | Theorems.Thm_Kyprianou_Ch03_levy_future_finDim_indep_pastSigma
-- name    : Kyprianou.Ch03.levy_future_finDim_indep_pastSigma
-- status  : Open
-- author  : @pageman
-- created : 2026-11-24T14:02:45.192798+00:00
-- url     : https://prove2.me/theorems/a03ebd61-8ffe-4337-b1e2-2f1b71c5c1b4
-- title:
--   Finite future increments IndepFun of finite past evaluations
-- statement:
--   For a Lévy process $X$ under a probability measure $P$, a time $\tau\ge 0$, and finite index sets $I\subset\mathbb{R}_{\ge 0}$ and $J\subset\{v:v\le\tau\}$, the random vectors
--   $$
--   \bigl(X_{\tau+u}-X_\tau\bigr)_{u\in I}
--   \qquad\text{and}\qquad
--   \bigl(X_v\bigr)_{v\in J}
--   $$
--   are independent.
--
--   This is the finite-dimensional (cylinder) form of Lévy independent increments needed to upgrade, via $\pi$-$\lambda$ / Mathlib process independence, to full path independence of the future increment process from $\mathrm{pastSigma}\,X\,\tau$.
--
--   **Formalization Note.** `IndepFun` of the finite future-increment map against the finite past-evaluation map on `Set.Iic τ`; uses Durrett `pastSigma` packaging from `Def_DurrettProbability_Brownian` and `IsLevyProcess` from LeanLevy.
-- source:
--   Kyprianou (2006) Ch.3 / Durrett §7.2; cylinder form of independent increments for Blumenthal path independence

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_DurrettProbability_Brownian
open MeasureTheory ProbabilityTheory DurrettProbability
open scoped NNReal
set_option autoImplicit false

namespace Kyprianou.Ch03

/-- Finite future increments after `τ` are independent of finite past evaluations up to `τ`.
Cylinder engine for path-level Lévy independence (Blumenthal). -/
theorem levy_future_finDim_indep_pastSigma
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (X : NNReal → Omega → Real)
    (hX : ProbabilityTheory.IsLevyProcess X P)
    (τ : NNReal)
    (I : Finset NNReal)
    (J : Finset (Set.Iic τ)) :
    IndepFun
      (fun ω (u : I) => X (τ + (u : NNReal)) ω - X τ ω)
      (fun ω (v : J) => X ((v : Set.Iic τ) : NNReal) ω)
      P := by
  sorry

end Kyprianou.Ch03
