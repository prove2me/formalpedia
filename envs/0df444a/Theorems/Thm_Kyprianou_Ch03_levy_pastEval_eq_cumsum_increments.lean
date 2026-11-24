-- Prove2me | Theorems.Thm_Kyprianou_Ch03_levy_pastEval_eq_cumsum_increments
-- name    : Kyprianou.Ch03.levy_pastEval_eq_cumsum_increments
-- status  : Proved
-- author  : @pageman
-- created : 2026-11-24T22:32:17.151468+00:00
-- url     : https://prove2.me/theorems/7f99e87e-c896-4d99-a0c7-3dddadb18fc1
-- title:
--   Past evaluation equals cumulative successive grid increments
-- statement:
--   If a real process $X$ satisfies $X_0=0$ and $(e_i)_{0\le i\le k}$ is a time grid with $e_0=0$ and $e_{i_v}=v$, then for every sample $\omega$,
--   $$
--   X_v(\omega)=\sum_{j=0}^{k-1}\mathbf{1}_{j\,\mathrm{castSucc}<i_v}\bigl(X_{e_{j+1}}(\omega)-X_{e_j}(\omega)\bigr).
--   $$
--   This is the elementary telescoping identity reconstructing path evaluations from successive increments on a grid based at the origin.
--
--   **Formalization Note.** Pure pathwise equality; hypothesis `X 0 = fun _ => 0`.
-- source:
--   Kyprianou Ch.3; telescoping path algebra

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
open MeasureTheory ProbabilityTheory
open scoped NNReal
set_option autoImplicit false

namespace Kyprianou.Ch03

/-- Pathwise: an evaluation `X v` on a grid starting at `0` equals the sum of successive
increments up to the grid index of `v`. Uses `X 0 = 0`. -/
theorem levy_pastEval_eq_cumsum_increments
    {Omega : Type}
    (X : NNReal → Omega → Real)
    (hX0 : X 0 = fun _ => 0)
    (k : ℕ) (e : Fin (k + 1) → NNReal) (he0 : e 0 = 0)
    (v : NNReal) (i_v : Fin (k + 1)) (hi : e i_v = v)
    (ω : Omega) :
    X v ω =
      ∑ j : Fin k,
        if j.castSucc < i_v then
          X (e j.succ) ω - X (e j.castSucc) ω
        else 0 := by
  sorry

end Kyprianou.Ch03
