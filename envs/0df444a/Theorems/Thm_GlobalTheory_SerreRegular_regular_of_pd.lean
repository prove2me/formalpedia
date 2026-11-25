-- Prove2me | Theorems.Thm_GlobalTheory_SerreRegular_regular_of_pd
-- name    : GlobalTheory.SerreRegular.regular_of_pd
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T00:07:07.72569+00:00
-- url     : https://prove2.me/theorems/d5815555-9bf9-40be-a5e9-e08476ce521a
-- title:
--   Serre Regular: regular of pd
-- statement:
--   The Serre Regular construction uses the regular of pd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/IsRegularLocalRingOfFlatOfMapEqMaximalIdeal.lean#L217-L286
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/IsRegularLocalRingOfFlatOfMapEqMaximalIdeal.lean#L217-L286

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

theorem GlobalTheory.SerreRegular.regular_of_pd (d : ℕ) : ∀ (A : Type) [CommRing A] [IsNoetherianRing A] [IsLocalRing A],
    (maximalIdeal A).spanFinrank = d →
    (∃ n, HasProjectiveDimensionLE (ModuleCat.of A (A ⧸ maximalIdeal A)) n) →
    IsRegularLocalRing A := by sorry
