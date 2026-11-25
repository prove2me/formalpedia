-- Prove2me | Theorems.Thm_GlobalTheory_AbCoh_pullHO1_surjective_of_smallExt
-- name    : GlobalTheory.AbCoh.pullHO1_surjective_of_smallExt
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T17:05:59.563745+00:00
-- url     : https://prove2.me/theorems/1737b445-fd59-508c-b6cc-6d546b7c5c47
-- title:
--   Ab Coh: pull HO1 surjective of small Ext
-- statement:
--   The Ab Coh construction uses the pull HO1 surjective of small Ext property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SmallExtensionPrimitiveLift.lean#L17-L49
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SmallExtensionPrimitiveLift.lean#L17-L49

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_AxesVanishingStructureSheafDegOne
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_IsScalarTowerOfAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_PreUMono
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__AbelianHodgeDeRham_0e03413a4fcf6a02
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsFlatLiftingObstructionClassStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsLiftOfLiftingObstructionEqZeroStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LiftingObstructionBocksteinAddStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ObstructionClassNaturalStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_GrpPullbackProdSelfIsPullbackStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SmallExtensionPrimitiveLift
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

theorem GlobalTheory.AbCoh.pullHO1_surjective_of_smallExt : ∀ (R R' R₀ : Type) [CommRing R] [CommRing R'] [CommRing R₀] (t : R) (σ : R →+* R') (σ₀ : R →+* R₀) (g : ℕ) (A : Over (Sp R)) [GrpObj A] (A' : Over (Sp R')) [GrpObj A'] (A₀ : Over (Sp R₀)) [GrpObj A₀] (φ : A'.left ⟶ A.left) (φ₀ : A₀.left ⟶ A.left) (h : IsGrpPullback A' A (spMap σ) φ) (h₀ : IsGrpPullback A₀ A (spMap σ₀) φ₀), SmallExt t σ σ₀ → IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → StructureSheafH1Primitive A' → NoPrimitiveStructureSheafH2 A₀ → Function.Surjective (pullHO1 h.1.w) := by sorry
