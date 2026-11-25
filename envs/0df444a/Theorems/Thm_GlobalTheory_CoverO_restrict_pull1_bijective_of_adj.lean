-- Prove2me | Theorems.Thm_GlobalTheory_CoverO_restrict_pull1_bijective_of_adj
-- name    : GlobalTheory.CoverO.restrict_pull1_bijective_of_adj
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T15:04:32.880551+00:00
-- url     : https://prove2.me/theorems/35e85ab9-6842-4061-8012-5489a2c3468b
-- title:
--   Cover O: restrict pull1 bijective of adj
-- statement:
--   The Cover O construction uses the restrict pull1 bijective of adj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/CechPullOneBijectiveLatticeCover.lean#L32-L49
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/CechPullOneBijectiveLatticeCover.lean#L32-L49

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_AxesVanishingStructureSheafDegOne
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_IsScalarTowerOfAlgebraMapEq
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__AbelianHodgeDeRham_0e03413a4fcf6a02
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CechPullOneBijectiveLatticeCover
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
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.CoverO

theorem GlobalTheory.CoverO.restrict_pull1_bijective_of_adj {R : Type} [CommRing R] {C C' : Type} [Category.{0} C]
    [Category.{0} C'] (F : C ⥤ CommAlgCat.{0} R) (G : C' ⥤ C) (H : C ⥤ C') (adj : G ⊣ H) :
    Function.Bijective (CoefMap.restrict F G).pull1 := by sorry
