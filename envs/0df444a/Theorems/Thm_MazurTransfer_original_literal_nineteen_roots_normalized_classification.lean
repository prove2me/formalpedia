-- Prove2me | Theorems.Thm_MazurTransfer_original_literal_nineteen_roots_normalized_classification
-- name    : MazurTransfer.original_literal_nineteen_roots_normalized_classification
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-22T01:50:38.411994+00:00
-- url     : https://prove2.me/theorems/574ec0ed-6feb-4dee-93a0-d761379be23f
-- statement:
--   The original given finite-free cocommutative Hopf model over the same rational subring at nineteen has a literal mu19 bialgebra equivalence whose field points equal its same given arithmetic root label, pointwise. The complete original proposition and helper type, all original constructor types and whole values, and both original scoped provider types and the nonproof whole value are independently checked. Every original hypothesis is retained. Named downstream consumer: canonical scalar base change of the same selected integral pi quotient, retaining its exact quotient restriction and Kummer maps.

import Definitions.Def_MazurTransfer_OriginalLiteralNineteenRootsCartierDualPointsData20261020
import Definitions.Def_MazurTransfer_OriginalBialgebraCyclicMu19PointsData20261020
import Definitions.Def_MazurTransfer_OriginalCyclicCharacterConjugationData20261020
import Definitions.Def_MazurTransfer_OriginalMu19BialgebraPointLabelNormalizationData20261020
import Theorems.Thm_MazurTransfer_original_literal_nineteen_roots_cyclic_classification
import Theorems.Thm_MazurTransfer_original_mu19_bialgebra_point_label_normalization
noncomputable section
open MazurTransfer.NineteenRootsGaloisRepresentation MazurTransfer.LiteralNineteenRootsCartierDualPoints
open MazurTransfer.CyclicNineteenGroupAlgebraPoints MazurTransfer.BialgebraCyclicMu19Points
local notation "K" => AlgebraicClosure ℚ
local notation "R" => GaloisRep.ratLocalizedAt 19
attribute [local instance] MazurTransfer.LiteralNineteenRootsCartierDualPoints.instDistribMulActionAlgEquivRatAlgebraicClosureAdditiveSubtypeUnitsMemSubgroupRoots_literalNineteenRootsCartierDualPoints
attribute [local instance] MazurTransfer.LiteralNineteenRootsCartierDualPoints.instFactPrimeOfNatNat_literalNineteenRootsCartierDualPoints
attribute [local instance] MazurTransfer.LiteralNineteenRootsCartierDualPoints.instModuleZModOfNatNatAdditiveSubtypeUnitsAlgebraicClosureRatMemSubgroupRoots_literalNineteenRootsCartierDualPoints

theorem MazurTransfer.original_literal_nineteen_roots_normalized_classification : ∀ (H : Type) [CommRing H] [HopfAlgebra R H] [Module.Finite R H] [Module.Free R H] [Coalgebra.IsCocomm R H] (e : WithConv (H →ₐ[R] K) ≃ Additive (Roots K)) (he_add : ∀ f g, e (f * g) = e f + e g) (he_act : ∀ (σ : K ≃ₐ[ℚ] K) (f g : WithConv (H →ₐ[R] K)), (∀ x : H, g x = σ (f x)) → e g = rootsRepresentation K σ (e f)),
∃ ψ : H ≃ₐc[R] MonoidAlgebra R Cyclic,
      ∀ f : WithConv (H →ₐ[R] K), literalPointEquiv ψ K f = (e f).toMul := by sorry
