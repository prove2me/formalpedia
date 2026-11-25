-- Prove2me | Theorems.Thm_GlobalTheory_exists_ringEquiv_integralClosure_padicInt
-- name    : GlobalTheory.exists_ringEquiv_integralClosure_padicInt
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T15:30:37.383067+00:00
-- url     : https://prove2.me/theorems/6e260953-6f1a-5e5d-8516-8a2b3027301d
-- title:
--   Global Theory: exists ring Equiv integral Closure padic Int
-- statement:
--   The Global Theory construction uses the exists ring Equiv integral Closure padic Int property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/NonemptyPadicIntRingHomOfIsAdicComplete.lean#L76-L158
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/NonemptyPadicIntRingHomOfIsAdicComplete.lean#L76-L158

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

theorem GlobalTheory.exists_ringEquiv_integralClosure_padicInt (V K : Type*) [CommRing V] [IsDomain V]
    [IsDiscreteValuationRing V] [IsAdicComplete (maximalIdeal V) V] [Field K] [CharZero K]
    [Algebra V K] [IsFractionRing V K] [Finite (ResidueField V)] :
    ∃ (p : ℕ) (_ : Fact p.Prime) (K₀ : IntermediateField ℚ_[p] (PadicAlgCl p)) (e : K ≃+* K₀)
      (e₀ : V ≃+* integralClosure ℤ_[p] K₀), FiniteDimensional ℚ_[p] K₀ ∧
      ∀ x, e (algebraMap V K x) = ((e₀ x : integralClosure ℤ_[p] K₀) : K₀) := by sorry
