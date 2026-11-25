-- Prove2me | Theorems.Thm_GlobalTheory_SerreRegular_projective_of_socle
-- name    : GlobalTheory.SerreRegular.projective_of_socle
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T00:07:09.475461+00:00
-- url     : https://prove2.me/theorems/a0b31af6-c07b-46a9-8375-105e9b9a57a7
-- title:
--   Serre Regular: projective of socle
-- statement:
--   The Serre Regular construction uses the projective of socle property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/IsRegularLocalRingOfFlatOfMapEqMaximalIdeal.lean#L80-L129
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/IsRegularLocalRingOfFlatOfMapEqMaximalIdeal.lean#L80-L129

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_ProjectionSurjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsHasProjectiveDimensionLEOfResidueField
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_CohenMacaulay_LocDim
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_MaximalIdealSquares_RingKrullDimQuotientSpanSingletonAddOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsRegularLocalRingOfFlatOfMapEqMaximalIdeal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing GlobalTheory.Pat CategoryTheory TensorProduct
open GlobalTheory
open GlobalTheory.SerreRegular

theorem GlobalTheory.SerreRegular.projective_of_socle {A : Type} [CommRing A] [IsNoetherianRing A] [IsLocalRing A] {a : A}
    (ha : a ≠ 0) (hm : ∀ y ∈ maximalIdeal A, a * y = 0) (n : ℕ) :
    ∀ (M : ModuleCat.{0} A) [Module.Finite A M], HasProjectiveDimensionLE M n →
      Module.Projective A M := by sorry
