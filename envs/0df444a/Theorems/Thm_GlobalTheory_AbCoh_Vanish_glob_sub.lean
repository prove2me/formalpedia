-- Prove2me | Theorems.Thm_GlobalTheory_AbCoh_Vanish_glob_sub
-- name    : GlobalTheory.AbCoh.Vanish.glob_sub
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T15:13:15.580647+00:00
-- url     : https://prove2.me/theorems/259cb940-5957-5b4d-87a9-b04f23c48a7d
-- title:
--   Vanish: glob sub
-- statement:
--   The Vanish construction uses the glob sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/CommAlgFunctorCohomologyTwoEqZeroOfIsInitial.lean#L27-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/CommAlgFunctorCohomologyTwoEqZeroOfIsInitial.lean#L27-L30

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_AxesVanishingStructureSheafDegOne
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_IsScalarTowerOfAlgebraMapEq
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__AbelianHodgeDeRham_0e03413a4fcf6a02
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CommAlgFunctorCohomologyTwoEqZeroOfIsInitial
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct Opposite
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.AbCoh GlobalTheory.AbCoh.Vanish

theorem GlobalTheory.AbCoh.Vanish.glob_sub {R : Type} [CommRing R] {C : Type} [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R) {T₀ : C}
    (h : IsInitial T₀) [Subsingleton Ω[F.obj T₀⁄R]] : Subsingleton (Glob1 F) := by sorry
