-- Prove2me | Theorems.Thm_GlobalTheory_AbCoh_CohBaseChange_liftsAt_of
-- name    : GlobalTheory.AbCoh.CohBaseChange.liftsAt_of
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T15:17:18.497601+00:00
-- url     : https://prove2.me/theorems/9a641706-e6c3-497a-af90-22138d97c33a
-- title:
--   Coh Base Change: lifts At of
-- statement:
--   The Coh Base Change construction uses the lifts At of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SpMapAlgHomAlgebraMap.lean#L44-L59
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SpMapAlgHomAlgebraMap.lean#L44-L59

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

theorem GlobalTheory.AbCoh.CohBaseChange.liftsAt_of (K : CochainComplex (ModuleCat.{0} R) ℕ) {R' k : Type} [CommRing R'] [Algebra R R']
    [CommRing k] [Algebra R k] (α : R' →ₐ[R] k) (i : ℕ) {H H₀ : Type} [AddCommGroup H] [Module R' H]
    [AddCommGroup H₀] [Module k H₀] (θ : LinearMap.ker (dB K R' i (i + 1)) →ₗ[R'] H)
    (θ₀ : LinearMap.ker (dB K k i (i + 1)) →ₗ[k] H₀) (p : H → H₀) (hθ : Function.Surjective θ)
    (hθ₀ : ∀ z, θ₀ z = 0 ↔ z.1 ∈ LinearMap.range (dB K k (i - 1) i))
    (nat : ∀ z z', z'.1 = ext α _ z.1 → θ₀ z' = p (θ z)) (hp : Function.Surjective p) : LiftsAt K α i := by sorry
