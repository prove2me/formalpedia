-- Prove2me | Theorems.Thm_MazurTransfer_original_literal_nineteen_roots_cartier_dual_point_laws
-- name    : MazurTransfer.original_literal_nineteen_roots_cartier_dual_point_laws
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-22T00:15:31.143272+00:00
-- url     : https://prove2.me/theorems/732e0427-26a6-4c43-82bc-82e65902ba63
-- statement:
--   For the same given finite-free cocommutative Hopf model with the original literal nineteenth-root arithmetic labels, its original Cartier dual field points are Galois fixed, have exponent nineteen and cardinality nineteen. The original chosen commutative group retains the original convolution monoid definitionally. Both complete original propositions and helper types, the original point group and chosen cyclic equivalence constructor types and whole values, and every original root and Cartier dual context are independently checked. All original hypotheses are retained. Named downstream consumer: normalized literal mu19 classification of the same selected integral pi quotient and its Kummer unit conditions.

import Definitions.Def_MazurTransfer_OriginalLiteralNineteenRootsCartierDualPointsData20261020
noncomputable section
open MazurTransfer.NineteenRootsGaloisRepresentation MazurTransfer.NineteenRootsCyclotomicPower MazurTransfer.LiteralNineteenRootsCartierDualPoints
local notation "K" => AlgebraicClosure ℚ
local notation "R" => GaloisRep.ratLocalizedAt 19
attribute [local instance] MazurTransfer.LiteralNineteenRootsCartierDualPoints.instDistribMulActionAlgEquivRatAlgebraicClosureAdditiveSubtypeUnitsMemSubgroupRoots_literalNineteenRootsCartierDualPoints
attribute [local instance] MazurTransfer.LiteralNineteenRootsCartierDualPoints.instFactPrimeOfNatNat_literalNineteenRootsCartierDualPoints
attribute [local instance] MazurTransfer.LiteralNineteenRootsCartierDualPoints.instModuleZModOfNatNatAdditiveSubtypeUnitsAlgebraicClosureRatMemSubgroupRoots_literalNineteenRootsCartierDualPoints

theorem MazurTransfer.original_literal_nineteen_roots_cartier_dual_point_laws : (∀ (H : Type) [CommRing H] [HopfAlgebra R H] [Module.Finite R H] [Module.Free R H] [Coalgebra.IsCocomm R H] (e : WithConv (H →ₐ[R] K) ≃ Additive (Roots K)) (he_add : ∀ f g, e (f * g) = e f + e g) (he_act : ∀ (σ : K ≃ₐ[ℚ] K) (f g : WithConv (H →ₐ[R] K)), (∀ x : H, g x = σ (f x)) → e g = rootsRepresentation K σ (e f)),
(∀ (σ : K ≃ₐ[ℚ] K) (ψ : DualPoints H) (θ : CartierDual R H), σ (ψ θ) = ψ θ) ∧
    (∀ ψ : DualPoints H, ψ ^ 19 = 1) ∧ Nat.card (DualPoints H) = 19) ∧ (∀ (H : Type) [CommRing H] [HopfAlgebra R H] [Module.Finite R H] [Module.Free R H] [Coalgebra.IsCocomm R H] (e : WithConv (H →ₐ[R] K) ≃ Additive (Roots K)) (he_add : ∀ f g, e (f * g) = e f + e g) (he_act : ∀ (σ : K ≃ₐ[ℚ] K) (f g : WithConv (H →ₐ[R] K)), (∀ x : H, g x = σ (f x)) → e g = rootsRepresentation K σ (e f)),
(dualPointGroup H e he_add he_act).toMonoid = (inferInstance : Monoid (DualPoints H))) := by sorry
