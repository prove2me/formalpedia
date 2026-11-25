-- Prove2me | Theorems.Thm_GlobalTheory_ThetaShiftProofs_j_over
-- name    : GlobalTheory.ThetaShiftProofs.j_over
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T12:41:49.489551+00:00
-- url     : https://prove2.me/theorems/aa7a81b5-ba87-5b18-a651-3d2f9719cdee
-- title:
--   Theta Shift Proofs: j over
-- statement:
--   The Theta Shift Proofs construction uses the j over property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/IsOpenImmersionJKPowerSeries.lean#L34-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/IsOpenImmersionJKPowerSeries.lean#L34-L37

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RigidSys
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_IsOpenImmersionJKPowerSeries
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.ThetaShiftProofs
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
variable {D : Datum H} {l : Level H} {Xo : Moduli D l} {c : Coeff l}

theorem GlobalTheory.ThetaShiftProofs.j_over {O : Type} [CommRing O] {β : O →+* c.F} (Y : Model Xo c β) :
    Y.j ≫ Y.s = pullback.snd _ _ ≫ spMap β := by sorry
