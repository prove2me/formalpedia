-- Prove2me | Theorems.Thm_GlobalTheory_AbCoh_CohBaseChange_liftsAt_zero
-- name    : GlobalTheory.AbCoh.CohBaseChange.liftsAt_zero
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T15:13:25.770047+00:00
-- url     : https://prove2.me/theorems/7b031b93-9384-5a39-aba8-50d0bdc6cdee
-- title:
--   Coh Base Change: lifts At zero
-- statement:
--   The Coh Base Change construction uses the lifts At zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SpMapAlgHomAlgebraMap.lean#L77-L98
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SpMapAlgHomAlgebraMap.lean#L77-L98

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_AxesVanishingStructureSheafDegOne
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_IsScalarTowerOfAlgebraMapEq
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__AbelianHodgeDeRham_0e03413a4fcf6a02
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SpMapAlgHomAlgebraMap
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
open GlobalTheory GlobalTheory.AbCoh GlobalTheory.AbCoh.CohBaseChange
variable {R : Type} [CommRing R]
variable {X : Scheme.{0}} {s : X ⟶ Sp R} {K : CochainComplex (ModuleCat.{0} R) ℕ}

theorem GlobalTheory.AbCoh.CohBaseChange.liftsAt_zero (M : Model s K) (hU : UConst s) {R' k : Type} [CommRing R'] [Algebra R R']
    [CommRing k] [Algebra R k] (α : R' →ₐ[R] k) (hα : Function.Surjective α) : LiftsAt K α 0 := by sorry
