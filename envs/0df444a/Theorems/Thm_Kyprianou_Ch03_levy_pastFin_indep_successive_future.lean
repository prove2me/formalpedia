-- Prove2me | Theorems.Thm_Kyprianou_Ch03_levy_pastFin_indep_successive_future
-- name    : Kyprianou.Ch03.levy_pastFin_indep_successive_future
-- status  : Open
-- author  : @pageman
-- created : 2026-11-24T17:22:32.385713+00:00
-- url     : https://prove2.me/theorems/40682958-eaf9-4bcb-adda-7266e4112a0b
-- title:
--   Past Finset evaluations IndepFun successive future increments
-- statement:
--   For a Lévy process $X$ under a probability $P$, a time $\tau\ge 0$, a finite set $J\subset\{v:v\le\tau\}$, and a monotone lag grid $(\ell_i)_{0\le i\le m}$ with $\ell_0=0$, the random vector of past evaluations
--   $$
--   \bigl(X_v\bigr)_{v\in J}
--   $$
--   is independent of the successive future increments
--   $$
--   X_{\tau+\ell_{i+1}}-X_{\tau+\ell_i},\qquad i=0,\ldots,m-1.
--   $$
--
--   This is the cut-at-$\tau$ form of independent increments needed to rebuild arbitrary finite future path increments by telescoping.
--
--   **Formalization Note.** `IndepFun` of the `Finset (Set.Iic τ)`-indexed evaluation map against the `Fin m`-indexed successive increment map; uses `IsLevyProcess` and Durrett packaging.
-- source:
--   Kyprianou (2006) Ch.3 / Durrett §7.2; cut-at-τ independent increments for Blumenthal cylinders

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_DurrettProbability_Brownian
open MeasureTheory ProbabilityTheory DurrettProbability
open scoped NNReal
set_option autoImplicit false

namespace Kyprianou.Ch03

/-- Finite past evaluations on `Iic τ` are independent of successive Lévy increments
along a monotone lag grid based at `τ`. Engine for finite-dimensional path independence. -/
theorem levy_pastFin_indep_successive_future
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (X : NNReal → Omega → Real)
    (hX : ProbabilityTheory.IsLevyProcess X P)
    (τ : NNReal)
    (J : Finset (Set.Iic τ))
    (m : ℕ) (lags : Fin (m + 1) → NNReal) (hlags : Monotone lags)
    (h0 : lags 0 = 0) :
    IndepFun
      (fun ω (v : J) => X ((v : Set.Iic τ) : NNReal) ω)
      (fun ω (i : Fin m) =>
        X (τ + lags i.succ) ω - X (τ + lags i.castSucc) ω)
      P := by
  sorry

end Kyprianou.Ch03
