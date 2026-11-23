-- Prove2me | Theorems.Thm_GlobalTheory_PhiGam_nab_apply_eq
-- name    : GlobalTheory.PhiGam.nab_apply_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:54:23.605587+00:00
-- url     : https://prove2.me/theorems/3dacc8a8-a8f5-4b4e-8317-ff67ec1264cc
-- title:
--   Phi Gam: nab apply eq
-- statement:
--   The Phi Gam construction uses the nab apply eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/PowerSeriesOneAddConstMulXMulInv.lean#L159-L160
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/PowerSeriesOneAddConstMulXMulInv.lean#L159-L160

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

theorem GlobalTheory.PhiGam.nab_apply_eq [Module k V] [IsScalarTower k k⸨X⸩ V] (g : V →ₗ[k] V) (x : V) :
    nab g x = (vv k)⁻¹ • (g x - x) := by sorry
