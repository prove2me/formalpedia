-- Prove2me | Theorems.Thm_GlobalTheory_ThetaShiftProofs_j_mem_abLocus
-- name    : GlobalTheory.ThetaShiftProofs.j_mem_abLocus
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T12:42:32.122503+00:00
-- url     : https://prove2.me/theorems/3b305ddd-ec6e-42c2-ba0d-7874fc33236d
-- title:
--   Theta Shift Proofs: j mem ab Locus
-- statement:
--   The Theta Shift Proofs construction uses the j mem ab Locus property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/IsOpenImmersionJKPowerSeries.lean#L24-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/IsOpenImmersionJKPowerSeries.lean#L24-L28

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

theorem GlobalTheory.ThetaShiftProofs.j_mem_abLocus {O : Type} [CommRing O] {β : O →+* c.F} (Y : Model Xo c β) (p : Xo.XF c) :
    Y.j p ∈ abLocus Y.t.G := by sorry
