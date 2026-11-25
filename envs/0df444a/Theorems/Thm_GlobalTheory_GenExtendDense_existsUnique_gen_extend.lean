-- Prove2me | Theorems.Thm_GlobalTheory_GenExtendDense_existsUnique_gen_extend
-- name    : GlobalTheory.GenExtendDense.existsUnique_gen_extend
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T01:10:20.807042+00:00
-- url     : https://prove2.me/theorems/a806838f-ec5b-4c55-923d-49b0d33707ab
-- title:
--   Gen Extend Dense: exists Unique gen extend
-- statement:
--   The Gen Extend Dense construction uses the exists Unique gen extend property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/ExistsUniqueGeneratorExtendDenseProOpen.lean#L54-L168
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/ExistsUniqueGeneratorExtendDenseProOpen.lean#L54-L168

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsMonHomOfMul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_PrecompleteBases_PsbLb
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsLineBundleGeneratorExtendingDensePart
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_IsIsoStalkMapOfFlatOfSurjectiveOnStalks
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExistsUniqueGeneratorExtendDenseProOpen
import Theorems.Thm_P2M_GlobalTheory_normal_domain_height_one__5612c3bf64ed

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
set_option backward.isDefEq.respectTransparency false
open GlobalTheory GlobalTheory.GenExtendDense
open GlobalTheory.GenericExtend GlobalTheory.DvrModel

theorem GlobalTheory.GenExtendDense.existsUnique_gen_extend : ∀ (Y U H HU X : Scheme.{0}) [IsLocallyNoetherian Y] (j : U ⟶ Y) [IsPreimmersion j] [Flat j] [IsDominant j] [QuasiCompact j], Geo.Tor.IsNormalScheme Y → ∀ (p : H ⟶ Y) (e : Y ⟶ H) (jH : HU ⟶ H) (pU : HU ⟶ U) (eU : U ⟶ HU), Smooth p → GeometricallyIntegral p → e ≫ p = 𝟙 _ → IsPullback jH pU p j → eU ≫ jH = j ≫ e → ∀ (L : LB X), L.IsLB → ∀ (I : Type) [Fintype I] (φ : I → (H ⟶ X)) (ε : I → ℤ) (t : LB.Gen (LB.LinComb L (fun i => jH ≫ φ i) ε)) (ρ : LB.Gen (LB.LinComb L (fun i => e ≫ φ i) ε)), t.IsGen → ρ.IsGen → LB.Gen.Corr L _ _ _ _ (LB.pullGen L _ _ t eU) (LB.pullGen L _ _ ρ j) → ∃! c : LB.Gen (LB.LinComb L φ ε), c.IsGen ∧ LB.pullGen L _ _ c jH = t := by sorry
