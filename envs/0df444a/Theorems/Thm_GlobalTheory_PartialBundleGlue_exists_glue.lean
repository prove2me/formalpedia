-- Prove2me | Theorems.Thm_GlobalTheory_PartialBundleGlue_exists_glue
-- name    : GlobalTheory.PartialBundleGlue.exists_glue
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T11:41:12.835428+00:00
-- url     : https://prove2.me/theorems/e57126a0-b816-4ee9-bb3a-0362f3531550
-- title:
--   Partial Bundle Glue: exists glue
-- statement:
--   The Partial Bundle Glue construction uses the exists glue property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsGlueRigidifiedPartialLineBundles.lean#L61-L106
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsGlueRigidifiedPartialLineBundles.lean#L61-L106

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsUniqueHom
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_FiniteHomogeneousInf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_BCTools
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SabPull
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_RigidifiedPartialLineBundleIsoCocycleStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsPartialBundleIsoNormalisedStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsGlueRigidifiedPartialLineBundles
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
open GlobalTheory GlobalTheory.PartialBundleGlue

theorem GlobalTheory.PartialBundleGlue.exists_glue : ∀ (X S : Scheme.{0}) (p : X ⟶ S) (e : S ⟶ X) (I : Type) (U : I → S.Opens) (M : I → LB X), e ≫ p = 𝟙 S → (∀ (V : S.Opens) (u : Γ(X, p ⁻¹ᵁ V)) (h : V ≤ e ⁻¹ᵁ (p ⁻¹ᵁ V)), (e.appLE _ V h).hom u = 1 → u = 1) → iSup U = ⊤ → (∀ i, ⨆ a, (M i).U a = p ⁻¹ᵁ U i) → (∀ i, ∀ (a : (M i).ι) (x : X), x ∈ (M i).U a → gm (𝟙 X) x ((M i).U a ⊓ (M i).U a) ((M i).g a a) = 1) → (∀ i, ∃ r : ((M i).pull e).Gen, r.IsGen) → (∀ i j, LBIso (M i) (M j)) → ∃ L : LB X, L.IsLB ∧ (∃ r : (L.pull e).Gen, r.IsGen) ∧ ∀ i, LBIso (M i) L := by sorry
