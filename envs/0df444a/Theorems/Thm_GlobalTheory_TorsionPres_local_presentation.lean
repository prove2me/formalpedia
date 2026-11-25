-- Prove2me | Theorems.Thm_GlobalTheory_TorsionPres_local_presentation
-- name    : GlobalTheory.TorsionPres.local_presentation
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T17:28:16.542337+00:00
-- url     : https://prove2.me/theorems/f3b100fd-bda6-5fb2-a343-61e60ebdceeb
-- title:
--   Torsion Pres: local presentation
-- statement:
--   The Torsion Pres construction uses the local presentation property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/TorsionLocalPresentationSmoothGroup.lean#L258-L362
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/TorsionLocalPresentationSmoothGroup.lean#L258-L362

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_Clauses
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_AlWellDefSt
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_PointEqOfSubsingleton
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_NilpotentCoordinates
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_PowEqScaleAndExistsUniqueTorsion
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_TorsionLocalPresentationSmoothGroup
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Pdiv GlobalTheory.AbLaw
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory GlobalTheory.TorsionPres

theorem GlobalTheory.TorsionPres.local_presentation : ∀ (O : Type) [CommRing O] [IsLocalRing O] (G : Over (Sp O)) [GrpObj G] [IsCommMonObj G] (n : ℕ) (H : Type) [CommRing H] [Algebra O H] [Module.Finite O H] (y : specO O H ⟶ G) (g : ℕ), SmoothOfRelativeDimension g G.hom → y ^ n = 1 → (∀ (S : Type) [CommRing S] [Algebra O S] (z : specO O S ⟶ G), z ^ n = 1 → ∃! φ : H →ₐ[O] S, ptMap φ ≫ y = z) → ∀ (ε : H →ₐ[O] O), ptMap ε ≫ y = 1 → ∀ (T : Type) [CommRing T] [Algebra H T] [Algebra O T] [IsScalarTower O H T] [IsLocalization.AtPrime T ((IsLocalRing.maximalIdeal O).comap ε)] (εT : T →ₐ[O] O), (∀ h, εT (algebraMap H T h) = ε h) → ∃ (S : Type) (_ : CommRing S) (_ : Algebra O S) (π : S →ₐ[O] T) (x : Fin g → S) (a : Matrix (Fin g) (Fin g) S) (ρ : S →+* MvPowerSeries (Fin g) (IsLocalRing.ResidueField O)), Function.Surjective π ∧ RingHom.ker π = Ideal.span (Set.range (a.mulVec x)) ∧ RingHom.ker εT = Ideal.span (Set.range fun i => π (x i)) ∧ (∀ i j, εT (π (a i j)) = if i = j then (n : O) else 0) ∧ (∀ i, ρ (x i) = MvPowerSeries.X i) ∧ ∀ c ∈ IsLocalRing.maximalIdeal O, ρ (algebraMap O S c) = 0 := by sorry
