-- Prove2me | Theorems.Thm_GlobalTheory_AbCoh_hasFrame_of_isBaseChange
-- name    : GlobalTheory.AbCoh.hasFrame_of_isBaseChange
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T15:06:03.559339+00:00
-- url     : https://prove2.me/theorems/23d25152-a96c-4419-aa66-f815e35489c3
-- title:
--   Ab Coh: has Frame of is Base Change
-- statement:
--   The Ab Coh construction uses the has Frame of is Base Change property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HasFrameOfIsBaseChange.lean#L11-L55
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HasFrameOfIsBaseChange.lean#L11-L55

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_AxesVanishingStructureSheafDegOne
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_IsScalarTowerOfAlgebraMapEq
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__AbelianHodgeDeRham_0e03413a4fcf6a02
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HasFrameOfIsBaseChange
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
open GlobalTheory GlobalTheory.AbCoh

theorem GlobalTheory.AbCoh.hasFrame_of_isBaseChange : ∀ (R : Type) [CommRing R] (C : Type) [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R), ∀ (W : Type) [AddCommGroup W] [Module R W] [Module.Finite R W] [Module.Projective R W] (j : W →ₗ[R] Glob1 F), (∀ T : C, ∃ e : W →ₗ[R] Ω[F.obj T⁄R], (∀ w, e w = (j w).1 T) ∧ IsBaseChange (F.obj T) e) → HasFrame F := by sorry
