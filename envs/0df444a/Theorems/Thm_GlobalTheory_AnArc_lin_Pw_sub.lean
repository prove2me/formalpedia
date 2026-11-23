-- Prove2me | Theorems.Thm_GlobalTheory_AnArc_lin_Pw_sub
-- name    : GlobalTheory.AnArc.lin_Pw_sub
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T12:12:25.183902+00:00
-- url     : https://prove2.me/theorems/0364a1e1-e87e-46cb-ac35-67e42dc945c3
-- title:
--   An Arc: lin Pw sub
-- statement:
--   The An Arc construction uses the lin Pw sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/FormalThetaSumShiftPeriodDiv.lean#L97-L107
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/FormalThetaSumShiftPeriodDiv.lean#L97-L107

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ArchimedeanThetaValues_DegeneratingToriPeriodMapEqBaseOfYEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ArchimedeanThetaValues_CoeffFSumDerivEqFderiv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_FormalThetaSumShiftPeriodDiv
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
open GlobalTheory.AnArc
variable {O : Type} [CommRing O] [StarRing O] (A : AnArc O)

theorem GlobalTheory.AnArc.lin_Pw_sub (w : ℂ) (la la' : A.La) :
    A.lin la (A.Pw w la') - A.lin la' (A.Pw w la) = -(2 * Real.pi * Complex.I * A.EF la la') := by sorry
