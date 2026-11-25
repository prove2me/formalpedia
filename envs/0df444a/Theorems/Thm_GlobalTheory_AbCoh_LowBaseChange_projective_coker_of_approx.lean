-- Prove2me | Theorems.Thm_GlobalTheory_AbCoh_LowBaseChange_projective_coker_of_approx
-- name    : GlobalTheory.AbCoh.LowBaseChange.projective_coker_of_approx
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T14:50:40.332693+00:00
-- url     : https://prove2.me/theorems/90a1c2cc-3726-45da-aa1b-ee3b4fe3a4bc
-- title:
--   Low Base Change: projective coker of approx
-- statement:
--   The Low Base Change construction uses the projective coker of approx property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/KrullDimLEIsLocalRingQuotPow.lean#L43-L100
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/KrullDimLEIsLocalRingQuotPow.lean#L43-L100

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_AxesVanishingStructureSheafDegOne
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_IsScalarTowerOfAlgebraMapEq
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__AbelianHodgeDeRham_0e03413a4fcf6a02
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExactAndKerBaseChangeOfForallResidueField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_KrullDimLEIsLocalRingQuotPow
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
open GlobalTheory GlobalTheory.AbCoh GlobalTheory.AbCoh.LowBaseChange
variable {R : Type} [CommRing R]

theorem GlobalTheory.AbCoh.LowBaseChange.projective_coker_of_approx [IsNoetherianRing R] {A B : Type} [AddCommGroup A] [Module R A]
    [AddCommGroup B] [Module R B] [Module.Finite R B] [Module.Projective R B] (f : A →ₗ[R] B)
    (hyp : ∀ (m : Ideal R) [m.IsMaximal] (n : ℕ) (a : A), f a ∈ m • (⊤ : Submodule R B) →
      ∃ y : A, f y ∈ m ^ (n + 1) • (⊤ : Submodule R B) ∧ f a - f y ∈ m • LinearMap.range f) :
    Module.Projective R (B ⧸ LinearMap.range f) := by sorry
