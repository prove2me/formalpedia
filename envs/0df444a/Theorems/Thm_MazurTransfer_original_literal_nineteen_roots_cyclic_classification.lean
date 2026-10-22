-- Prove2me | Theorems.Thm_MazurTransfer_original_literal_nineteen_roots_cyclic_classification
-- name    : MazurTransfer.original_literal_nineteen_roots_cyclic_classification
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-22T01:17:07.729966+00:00
-- url     : https://prove2.me/theorems/c3f7096f-2f07-4d79-ae11-eaf23d6a0eb4
-- statement:
--   The original given finite-free cocommutative Hopf model with its fixed literal nineteenth-root arithmetic labels has the same original cyclic group-algebra classification, retaining its original chosen Cartier dual cyclic equivalence and exact evaluation identity. The complete original proposition and helper type, all original constructor types and whole values, and both original scoped provider types and their nonproof whole value are independently checked. Every original hypothesis is retained. Named downstream consumer: normalization of the same selected integral pi quotient arithmetic labels and norm Kummer unit conditions at nineteen.

import Definitions.Def_MazurTransfer_OriginalLiteralNineteenRootsCartierDualPointsData20261020
import Theorems.Thm_MazurTransfer_original_literal_nineteen_roots_hopf_classification
noncomputable section
open MazurTransfer.NineteenRootsGaloisRepresentation MazurTransfer.LiteralNineteenRootsCartierDualPoints
local notation "K" => AlgebraicClosure ℚ
local notation "R" => GaloisRep.ratLocalizedAt 19
attribute [local instance] MazurTransfer.LiteralNineteenRootsCartierDualPoints.instDistribMulActionAlgEquivRatAlgebraicClosureAdditiveSubtypeUnitsMemSubgroupRoots_literalNineteenRootsCartierDualPoints
attribute [local instance] MazurTransfer.LiteralNineteenRootsCartierDualPoints.instFactPrimeOfNatNat_literalNineteenRootsCartierDualPoints
attribute [local instance] MazurTransfer.LiteralNineteenRootsCartierDualPoints.instModuleZModOfNatNatAdditiveSubtypeUnitsAlgebraicClosureRatMemSubgroupRoots_literalNineteenRootsCartierDualPoints

theorem MazurTransfer.original_literal_nineteen_roots_cyclic_classification : ∀ (H : Type) [CommRing H] [HopfAlgebra R H] [Module.Finite R H] [Module.Free R H] [Coalgebra.IsCocomm R H] (e : WithConv (H →ₐ[R] K) ≃ Additive (Roots K)) (he_add : ∀ f g, e (f * g) = e f + e g) (he_act : ∀ (σ : K ≃ₐ[ℚ] K) (f g : WithConv (H →ₐ[R] K)), (∀ x : H, g x = σ (f x)) → e g = rootsRepresentation K σ (e f)),
∃ φ : H ≃ₐc[R] MonoidAlgebra R (Multiplicative (ZMod 19)),
      ∀ (k : Multiplicative (ZMod 19)) (θ : CartierDual R H),
        algebraMap R K (θ (φ.symm (MonoidAlgebra.single k 1))) =
          ((cyclicEquiv H e he_add he_act).symm k) θ := by sorry
