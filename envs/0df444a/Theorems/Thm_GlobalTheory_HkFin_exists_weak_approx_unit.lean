-- Prove2me | Theorems.Thm_GlobalTheory_HkFin_exists_weak_approx_unit
-- name    : GlobalTheory.HkFin.exists_weak_approx_unit
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:03:27.592711+00:00
-- url     : https://prove2.me/theorems/faa82cbf-e85b-4ade-9dc6-0a7376f6d7a1
-- title:
--   Hk Fin: exists weak approx unit
-- statement:
--   The Hk Fin construction uses the exists weak approx unit property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SatakeParameters/ExistsWeakApproxUnitFinitePlace.lean#L8-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SatakeParameters/ExistsWeakApproxUnitFinitePlace.lean#L8-L34

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FiniteOrderValuation_WeakApprox
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_ExistsWeakApproxUnitFinitePlace
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum WithZero
open GlobalTheory GlobalTheory.HkFin

theorem GlobalTheory.HkFin.exists_weak_approx_unit (E : Type) [Field E] [NumberField E] (S : Finset (HeightOneSpectrum (𝓞 E)))
    (w : HeightOneSpectrum (𝓞 E)) (x : (w.adicCompletion E)ˣ) (n : ℕ) :
    ∃ y : E, y ≠ 0 ∧ Valued.v ((y : w.adicCompletion E) * ((x⁻¹ : (w.adicCompletion E)ˣ) : w.adicCompletion E) - 1)
      ≤ WithZero.exp (-(n : ℤ)) ∧ ∀ v ∈ S, v ≠ w → v.valuation E (y - 1) ≤ WithZero.exp (-(n : ℤ)) := by sorry
