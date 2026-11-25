-- Prove2me | Theorems.Thm_GlobalTheory_PhiGam_IsLat_shift
-- name    : GlobalTheory.PhiGam.IsLat.shift
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T12:15:22.148956+00:00
-- url     : https://prove2.me/theorems/93d9001d-d4b3-4b0c-8f08-ffb16933483e
-- title:
--   Is Lat: shift
-- statement:
--   The Is Lat construction uses the shift property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/PowerSeriesOneAddConstMulXMulInv.lean#L143-L149
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/PowerSeriesOneAddConstMulXMulInv.lean#L143-L149

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_PowerSeriesOneAddConstMulXMulInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.PhiGam
open scoped LaurentSeries PowerSeries
variable {k : Type} [Field k] {V : Type} [AddCommGroup V] [Module k⸨X⸩ V]
variable [Module k⟦X⟧ V] [IsScalarTower k⟦X⟧ k⸨X⸩ V]

theorem GlobalTheory.PhiGam.IsLat.shift {N : Submodule k⟦X⟧ V} (h : IsLat N) (a : ℤ) : IsLat (sh a N) := by sorry
