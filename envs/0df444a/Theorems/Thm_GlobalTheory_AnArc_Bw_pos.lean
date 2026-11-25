-- Prove2me | Theorems.Thm_GlobalTheory_AnArc_Bw_pos
-- name    : GlobalTheory.AnArc.Bw_pos
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T11:55:43.96766+00:00
-- url     : https://prove2.me/theorems/7d265f96-3006-42ba-8496-ad0d854b2214
-- title:
--   An Arc: Bw pos
-- statement:
--   The An Arc construction uses the Bw pos property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/TorusProjPeriodZeroEqReal.lean#L263-L271
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/TorusProjPeriodZeroEqReal.lean#L263-L271

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

theorem GlobalTheory.AnArc.Bw_pos {w : ℂ} (hw : (A.BwMat w).PosDef) {y : A.X} (hy : y ≠ 0) : 0 < A.Bw w y y := by sorry
