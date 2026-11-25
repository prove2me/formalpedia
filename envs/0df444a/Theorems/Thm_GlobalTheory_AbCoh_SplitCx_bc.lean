-- Prove2me | Theorems.Thm_GlobalTheory_AbCoh_SplitCx_bc
-- name    : GlobalTheory.AbCoh.SplitCx.bc
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T14:50:56.642622+00:00
-- url     : https://prove2.me/theorems/986c1ddd-a1ef-466f-a4c8-58d0f74ba49f
-- title:
--   Split Cx: bc
-- statement:
--   The Split Cx construction uses the bc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/CohomSplitBaseChange.lean#L77-L111
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/CohomSplitBaseChange.lean#L77-L111

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_AxesVanishingStructureSheafDegOne
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_IsScalarTowerOfAlgebraMapEq
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__AbelianHodgeDeRham_0e03413a4fcf6a02
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CohomSplitBaseChange
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
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.AbCoh GlobalTheory.AbCoh.SplitCx
variable {R : Type} [CommRing R]

theorem GlobalTheory.AbCoh.SplitCx.bc {M0 M1 M2 P : Type} [AddCommGroup M0] [Module R M0] [AddCommGroup M1] [Module R M1]
    [AddCommGroup M2] [Module R M2] [AddCommGroup P] [Module R P]
    (d0 : M0 →ₗ[R] M1) (d1 : M1 →ₗ[R] M2) (π : M1 →ₗ[R] P) (σ : P →ₗ[R] M1)
    (a : M1 →ₗ[R] M0) (b : M2 →ₗ[R] M1)
    (hπσ : π ∘ₗ σ = LinearMap.id) (hπd : π ∘ₗ d0 = 0) (hdσ : d1 ∘ₗ σ = 0)
    (hid : LinearMap.id = σ ∘ₗ π + d0 ∘ₗ a + b ∘ₗ d1) (S : Type) [CommRing S] [Algebra R S] :
    Function.Surjective (fun z : LinearMap.ker (d1.baseChange S) => π.baseChange S z.1) ∧
      ∀ z : LinearMap.ker (d1.baseChange S),
        π.baseChange S z.1 = 0 ↔ z.1 ∈ LinearMap.range (d0.baseChange S) := by sorry
