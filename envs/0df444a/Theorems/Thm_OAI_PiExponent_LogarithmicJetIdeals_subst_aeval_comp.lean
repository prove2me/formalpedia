-- Prove2me | Theorems.Thm_OAI_PiExponent_LogarithmicJetIdeals_subst_aeval_comp
-- name    : OAI.PiExponent.LogarithmicJetIdeals.subst_aeval_comp
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-16T05:57:53.422756+00:00
-- url     : https://prove2.me/theorems/03405d18-61af-44f2-80ac-f4777f2711a7
-- title:
--   Substitution of a polynomial evaluation composes its coordinates
-- statement:
--   For an admissible substitution b, substituting b into a polynomial evaluated at a is evaluation at the coordinates obtained by substituting b into a.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Approximation/AdmissibleMatrixGeometry.lean#L41-L44

import Mathlib.Data.Complex.Basic
import Mathlib.RingTheory.MvPowerSeries.Substitution

theorem OAI.PiExponent.LogarithmicJetIdeals.subst_aeval_comp
    {m : ℕ}
    (a b : Fin (m + 1) → MvPowerSeries (Fin (m + 1)) ℂ)
    (ha : MvPowerSeries.HasSubst a) (hb : MvPowerSeries.HasSubst b)
    (Q : MvPolynomial (Fin (m + 1)) ℂ) :
    MvPowerSeries.subst b (MvPolynomial.aeval a Q) =
      MvPolynomial.aeval (fun i => MvPowerSeries.subst b (a i)) Q := by sorry
