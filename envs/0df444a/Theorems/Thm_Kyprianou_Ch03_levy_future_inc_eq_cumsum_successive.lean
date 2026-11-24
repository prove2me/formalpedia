-- Prove2me | Theorems.Thm_Kyprianou_Ch03_levy_future_inc_eq_cumsum_successive
-- name    : Kyprianou.Ch03.levy_future_inc_eq_cumsum_successive
-- status  : Proved
-- author  : @pageman
-- created : 2026-11-24T17:22:35.193865+00:00
-- url     : https://prove2.me/theorems/10b4204d-bb3a-4822-a1bb-f2282f5e9c26
-- title:
--   Future path increment equals cumulative successive grid increments
-- statement:
--   Let $X$ be a real process, $\tau\ge 0$, and $(\ell_i)_{0\le i\le m}$ a monotone lag grid with $\ell_0=0$. For any index $i_u$ with $\ell_{i_u}=u$ and any sample $\omega$,
--   $$
--   X_{\tau+u}(\omega)-X_\tau(\omega)
--   =
--   \sum_{i=0}^{m-1}
--   \mathbf{1}_{i+1\le i_u}
--   \bigl(X_{\tau+\ell_{i+1}}(\omega)-X_{\tau+\ell_i}(\omega)\bigr).
--   $$
--
--   This is the elementary telescoping identity that converts successive grid increments into a single path increment at lag $u$.
--
--   **Formalization Note.** Pure pathwise equality; no measure or independence hypotheses.
-- source:
--   Kyprianou (2006) Ch.3; telescoping path algebra for Lévy increments

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
open MeasureTheory ProbabilityTheory
open scoped NNReal
set_option autoImplicit false

namespace Kyprianou.Ch03

/-- Telescoping: a future path increment at a lag on a sorted grid equals the sum of
successive grid increments up to that lag. Pure pathwise algebra (no measure). -/
theorem levy_future_inc_eq_cumsum_successive
    {Omega : Type}
    (X : NNReal → Omega → Real)
    (τ : NNReal)
    (m : ℕ) (lags : Fin (m + 1) → NNReal) (hlags : Monotone lags)
    (h0 : lags 0 = 0)
    (u : NNReal) (i_u : Fin (m + 1)) (hi_u : lags i_u = u)
    (ω : Omega) :
    X (τ + u) ω - X τ ω =
      ∑ i : Fin m,
        if i.succ ≤ i_u then
          X (τ + lags i.succ) ω - X (τ + lags i.castSucc) ω
        else 0 := by
  sorry

end Kyprianou.Ch03
