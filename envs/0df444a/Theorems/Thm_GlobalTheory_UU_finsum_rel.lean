-- Prove2me | Theorems.Thm_GlobalTheory_UU_finsum_rel
-- name    : GlobalTheory.UU.finsum_rel
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T16:40:15.826476+00:00
-- url     : https://prove2.me/theorems/d158bd3a-377f-4ce5-a8b8-afe57d355bd3
-- title:
--   UU: finsum rel
-- statement:
--   The UU construction uses the finsum rel property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/AdicSumRel.lean#L21-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/AdicSumRel.lean#L21-L34

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PhiGenPf
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_WCompat
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_ExistsUniqueSamePt
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_SvalTwistOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_AdicSumRel
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
set_option autoImplicit false
open GlobalTheory GlobalTheory.UU

theorem GlobalTheory.UU.finsum_rel {A : Type*} [CommRing A] {Ix Ix' : Type*} (σ : Ix ≃ Ix') (f : Ix → A) (g : Ix' → A)
    (a b v : A) (s : Finset Ix) (s' : Finset Ix') (hf : ∀ i ∉ s, f i = 0) (hg : ∀ i ∉ s', g i = 0)
    (h : ∀ i, a * g (σ i) = b * (f i * v)) :
    a * ∑ i ∈ s', g i = b * ((∑ i ∈ s, f i) * v) := by sorry
