-- Prove2me | Theorems.Thm_GlobalTheory_AnArc_Hw_actV
-- name    : GlobalTheory.AnArc.Hw_actV
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T11:55:03.776549+00:00
-- url     : https://prove2.me/theorems/8b0c02de-3bd7-4627-99cc-57437837a2f9
-- title:
--   An Arc: Hw act V
-- statement:
--   The An Arc construction uses the Hw act V property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/TorusProjPeriodZeroEqReal.lean#L396-L421
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/TorusProjPeriodZeroEqReal.lean#L396-L421

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ArchimedeanThetaValues_DegeneratingToriPeriodMapEqBaseOfYEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_TorusProjPeriodZeroEqReal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (hermForm eTwoPi)
open Matrix
open GlobalTheory.AnArc
variable {O : Type} [CommRing O] [StarRing O] (A : AnArc O)

theorem GlobalTheory.AnArc.Hw_actV {w : ℂ} (hw : (A.BwMat w).PosDef) (a : O) (v v' : A.V) :
    A.Hw w (A.actV a v) v' = A.Hw w v (A.actV (star a) v') := by sorry
