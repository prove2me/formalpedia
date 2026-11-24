-- Prove2me | Theorems.Thm_Kyprianou_Ch03_levy_pastIncs_indep_successive_future
-- name    : Kyprianou.Ch03.levy_pastIncs_indep_successive_future
-- status  : Open
-- author  : @pageman
-- created : 2026-11-24T22:32:16.564869+00:00
-- url     : https://prove2.me/theorems/4d168c24-ea9c-4960-9686-4fef15bf92b0
-- title:
--   Past successive increments IndepFun future successive increments
-- statement:
--   For a Lévy process $X$ under $P$, a cut time $\tau$, a monotone past grid $(e_i)_{0\le i\le k}$ with $e_0=0$, $e_k=\tau$ and $e_i\le\tau$, and a monotone lag grid $(\ell_i)_{0\le i\le m}$ with $\ell_0=0$, the successive past increments
--   $$
--   X_{e_{j+1}}-X_{e_j},\qquad j<k,
--   $$
--   are independent of the successive future increments
--   $$
--   X_{\tau+\ell_{i+1}}-X_{\tau+\ell_i},\qquad i<m.
--   $$
--   This is the cut-at-$\tau$ packaging of independent increments on a concatenated monotone time grid.
--
--   **Formalization Note.** `IndepFun` of two `Fin`-indexed increment maps; requires coordinate measurability.
-- source:
--   Kyprianou Ch.3 / Durrett §7.2; HasIndependentIncrements cut at τ

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
open MeasureTheory ProbabilityTheory
open scoped NNReal
set_option autoImplicit false

namespace Kyprianou.Ch03

/-- Successive increments on a past grid ending at `τ` are `IndepFun` of successive
increments along a post-`τ` lag grid. Packaging of `HasIndependentIncrements` via
concatenated monotone times and `iIndepFun.indepFun_finset`. -/
theorem levy_pastIncs_indep_successive_future
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (X : NNReal → Omega → Real)
    (hX : ProbabilityTheory.IsLevyProcess X P)
    (τ : NNReal)
    (k : ℕ) (e : Fin (k + 1) → NNReal) (he0 : e 0 = 0) (he_mono : Monotone e)
    (helast : e (Fin.last k) = τ) (he_le : ∀ i, e i ≤ τ)
    (m : ℕ) (lags : Fin (m + 1) → NNReal) (hlags : Monotone lags) (h0 : lags 0 = 0)
    (hXmeas : ∀ t : NNReal, Measurable (X t)) :
    IndepFun
      (fun ω (j : Fin k) => X (e j.succ) ω - X (e j.castSucc) ω)
      (fun ω (i : Fin m) => X (τ + lags i.succ) ω - X (τ + lags i.castSucc) ω)
      P := by
  sorry

end Kyprianou.Ch03
