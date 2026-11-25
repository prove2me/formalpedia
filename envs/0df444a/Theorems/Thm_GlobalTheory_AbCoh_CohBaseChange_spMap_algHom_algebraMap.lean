-- Prove2me | Theorems.Thm_GlobalTheory_AbCoh_CohBaseChange_spMap_algHom_algebraMap
-- name    : GlobalTheory.AbCoh.CohBaseChange.spMap_algHom_algebraMap
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T15:02:08.843117+00:00
-- url     : https://prove2.me/theorems/08b1b9ce-8f83-4364-b522-41430244ce09
-- title:
--   Coh Base Change: sp Map alg Hom algebra Map
-- statement:
--   The Coh Base Change construction uses the sp Map alg Hom algebra Map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SpMapAlgHomAlgebraMap.lean#L35-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SpMapAlgHomAlgebraMap.lean#L35-L37

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

theorem GlobalTheory.AbCoh.CohBaseChange.spMap_algHom_algebraMap {R' R'' : Type} [CommRing R'] [Algebra R R'] [CommRing R''] [Algebra R R'']
    (α : R' →ₐ[R] R'') : spMap (α : R' →+* R'') ≫ spMap (algebraMap R R') = spMap (algebraMap R R'') := by sorry
