-- Prove2me | Theorems.Thm_GlobalTheory_SerreRegular_pd_flat
-- name    : GlobalTheory.SerreRegular.pd_flat
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T00:07:11.246293+00:00
-- url     : https://prove2.me/theorems/8c13da62-1b72-471b-b1f6-b26e10d84705
-- title:
--   Serre Regular: pd flat
-- statement:
--   The Serre Regular construction uses the pd flat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/IsRegularLocalRingOfFlatOfMapEqMaximalIdeal.lean#L44-L49
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/IsRegularLocalRingOfFlatOfMapEqMaximalIdeal.lean#L44-L49

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

theorem GlobalTheory.SerreRegular.pd_flat {A B : Type} [CommRing A] [IsNoetherianRing A] [CommRing B] [Algebra A B]
    [Module.Flat A B] (n : ℕ) (M : ModuleCat.{0} A) [Module.Finite A M]
    (h : HasProjectiveDimensionLE M n) : HasProjectiveDimensionLE (ModuleCat.of B (B ⊗[A] M)) n := by sorry
