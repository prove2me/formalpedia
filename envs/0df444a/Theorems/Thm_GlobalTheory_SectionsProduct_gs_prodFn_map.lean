-- Prove2me | Theorems.Thm_GlobalTheory_SectionsProduct_gs_prodFn_map
-- name    : GlobalTheory.SectionsProduct.gs_prodFn_map
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T19:52:34.030812+00:00
-- url     : https://prove2.me/theorems/997fc0d8-f29c-4b3e-af2b-621a95dda35b
-- title:
--   Sections Product: gs prod Fn map
-- statement:
--   The Sections Product construction uses the gs prod Fn map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/SectionLinCombFiberProductSeparated.lean#L240-L247
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/SectionLinCombFiberProductSeparated.lean#L240-L247

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DivCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_MemRangeRTensorOfForallDual
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_SectionLinCombFiberProductSeparated
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
open TensorProduct TopologicalSpace
noncomputable section
open GlobalTheory GlobalTheory.SectionsProduct
open GlobalTheory.KuennethOne
variable {B Y T S X₁ X₂ W : Scheme.{0}} {L : LB B} {K : Type} [Fintype K]
variable {p : W ⟶ X₁} {q : W ⟶ X₂} {i₁ : X₁ ⟶ S} {i₂ : X₂ ⟶ S} (H : IsPullback p q i₁ i₂)
variable {U U' : X₁.Opens} {V V' : X₂.Opens} (r : T ⟶ W) (z : T) (hz : r z ∈ p ⁻¹ᵁ U ⊓ q ⁻¹ᵁ V)
include hz

theorem GlobalTheory.SectionsProduct.gs_prodFn_map (hz' : r z ∈ p ⁻¹ᵁ U' ⊓ q ⁻¹ᵁ V') (f : Fn i₁ U →ₗ[Γ(S, ⊤)] Fn i₁ U')
    (g : Fn i₂ V →ₗ[Γ(S, ⊤)] Fn i₂ V') (c d : T.presheaf.stalk z)
    (hf : ∀ a, gs (r ≫ p) z U' (f a) = c * gs (r ≫ p) z U a) (hg : ∀ a, gs (r ≫ q) z V' (g a) = d * gs (r ≫ q) z V a)
    (t) : gs r z _ (prodFn H U' V' (TensorProduct.map f g t)) = c * d * gs r z _ (prodFn H U V t) := by sorry
