-- Prove2me | Theorems.Thm_GlobalTheory_exists_padicInt_algebra_finite
-- name    : GlobalTheory.exists_padicInt_algebra_finite
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T15:17:28.417437+00:00
-- url     : https://prove2.me/theorems/8623c615-1c97-488e-8aff-9a441c25ed9c
-- title:
--   Global Theory: exists padic Int algebra finite
-- statement:
--   The Global Theory construction uses the exists padic Int algebra finite property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/NonemptyPadicIntRingHomOfIsAdicComplete.lean#L40-L72
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/NonemptyPadicIntRingHomOfIsAdicComplete.lean#L40-L72

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IsDiscreteValuationRingIntegralClosurePadicInt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_BoundedOnFramesIffIntegralOnFrames
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_NonemptyPadicIntRingHomOfIsAdicComplete
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing
open GlobalTheory
open IsLocalRing

theorem GlobalTheory.exists_padicInt_algebra_finite (V : Type*) [CommRing V] [IsDomain V]
    [IsDiscreteValuationRing V] [IsAdicComplete (maximalIdeal V) V] [CharZero V]
    [Finite (ResidueField V)] :
    ∃ (p : ℕ) (_ : Fact p.Prime) (_ : Algebra ℤ_[p] V), Module.Finite ℤ_[p] V := by sorry
