-- Prove2me | Theorems.Thm_GlobalTheory_T_small_extension_primitive_lift
-- name    : GlobalTheory.T.small_extension_primitive_lift
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T17:23:20.994427+00:00
-- url     : https://prove2.me/theorems/57de4fe0-5ef6-591e-b4eb-c753f0e034f8
-- title:
--   T: small extension primitive lift
-- statement:
--   The T construction uses the small extension primitive lift property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SmallExtensionPrimitiveLiftStatement.lean#L12-L13
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SmallExtensionPrimitiveLiftStatement.lean#L12-L13

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SmallExtensionPrimitiveLift
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_AxesVanishingStructureSheafDegOne
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_IsScalarTowerOfAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_PreUMono
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__AbelianHodgeDeRham_0e03413a4fcf6a02
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SmallExtensionPrimitiveLiftStatement
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
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.small_extension_primitive_lift : ∀ (R R' R₀ : Type) [CommRing R] [CommRing R'] [CommRing R₀] (t : R) (σ : R →+* R') (σ₀ : R →+* R₀) (g : ℕ) (A : Over (Sp R)) [GrpObj A] (A' : Over (Sp R')) [GrpObj A'] (A₀ : Over (Sp R₀)) [GrpObj A₀] (φ : A'.left ⟶ A.left) (φ₀ : A₀.left ⟶ A.left) (h : IsGrpPullback A' A (spMap σ) φ) (h₀ : IsGrpPullback A₀ A (spMap σ₀) φ₀), SmallExt t σ σ₀ → IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → StructureSheafH1Primitive A' → NoPrimitiveStructureSheafH2 A₀ → Function.Surjective (pullHO1 h.1.w) := by sorry
