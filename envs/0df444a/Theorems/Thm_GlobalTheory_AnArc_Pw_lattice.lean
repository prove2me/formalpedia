-- Prove2me | Theorems.Thm_GlobalTheory_AnArc_Pw_lattice
-- name    : GlobalTheory.AnArc.Pw_lattice
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T12:40:41.103878+00:00
-- url     : https://prove2.me/theorems/91d85817-36ad-4e0e-9bcb-cceb3ebefc74
-- title:
--   An Arc: Pw lattice
-- statement:
--   The An Arc construction uses the Pw lattice property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/TorusProjPeriodZeroEqReal.lean#L391-L394
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/TorusProjPeriodZeroEqReal.lean#L391-L394

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

theorem GlobalTheory.AnArc.Pw_lattice {w : ℂ} (hw : (A.BwMat w).PosDef) : Function.Injective (A.Pw w) ∧
    DiscreteTopology (A.Pw w).range ∧ Submodule.span ℝ (Set.range (A.Pw w)) = ⊤ := by sorry
