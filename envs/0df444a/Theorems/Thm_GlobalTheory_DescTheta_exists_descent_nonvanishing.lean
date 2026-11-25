-- Prove2me | Theorems.Thm_GlobalTheory_DescTheta_exists_descent_nonvanishing
-- name    : GlobalTheory.DescTheta.exists_descent_nonvanishing
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T14:42:16.155784+00:00
-- url     : https://prove2.me/theorems/dad12dc2-0664-5fae-b32b-156c9f163eff
-- title:
--   Desc Theta: exists descent nonvanishing
-- statement:
--   The Desc Theta construction uses the exists descent nonvanishing property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsSecOnNonvanishingOfTameQuotient.lean#L268-L330
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsSecOnNonvanishingOfTameQuotient.lean#L268-L330

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RigidSys
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_Splits
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GtBaseChangeSt
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_BijectiveSmulChartSec
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_IsQuasicoherentOfForallExistsAffine
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsSumSmulSeparatingInertia
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsActionOfIsPullback
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsSmulApplyEqOfEqOnInvariants
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsSecOnNonvanishingOfTameQuotient
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
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory GlobalTheory.DescTheta
open GlobalTheory.LB
variable {X Y : Scheme.{0}}

theorem GlobalTheory.DescTheta.exists_descent_nonvanishing {Γ : Type} [Group Γ] [Finite Γ] {X' G G' : Scheme.{0}}
    (ρ : Γ →* Aut X) (π : X ⟶ X') (p : G ⟶ X) (p' : G' ⟶ X') (φ : G ⟶ G') (τ : Γ →* Aut G)
    (hπ : ∀ g, (ρ g).hom ≫ π = π) (w : φ ≫ p' = p ≫ π) (hφ : ∀ g, (τ g).hom ≫ φ = φ)
    (hp : ∀ g, (τ g).hom ≫ p = p ≫ (ρ g).hom)
    (hq : ∀ V : G'.Opens, Function.Injective (φ.app V).hom ∧ ∀ f : Γ(G, φ ⁻¹ᵁ V),
      (∀ g (h : φ ⁻¹ᵁ V ≤ (τ g).hom ⁻¹ᵁ (φ ⁻¹ᵁ V)), ((τ g).hom.appLE _ _ h).hom f = f) →
        f ∈ Set.range (φ.app V).hom)
    (htame : ∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ X),
      (Nat.card {g // x ≫ (ρ g).hom = x} : k) ≠ 0)
    (hfib : ∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ X) g, x ≫ (ρ g).hom = x →
      pullback.fst p x ≫ (τ g).hom = pullback.fst p x)
    {L : LB G'} {V : X'.Opens} (hW : IsAffineOpen (π ⁻¹ᵁ V))
    (s : Γ(toMod (L.pull φ), φ ⁻¹ᵁ p' ⁻¹ᵁ V)) (u : G) (hs : ∃ j, u ∈ G.basicOpen (coord s j)) :
    ∃ (t : Γ(toMod L, p' ⁻¹ᵁ V)) (i : L.ι), φ u ∈ G'.basicOpen (coord t i) := by sorry
