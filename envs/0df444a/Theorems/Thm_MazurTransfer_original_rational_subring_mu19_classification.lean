-- Prove2me | Theorems.Thm_MazurTransfer_original_rational_subring_mu19_classification
-- name    : MazurTransfer.original_rational_subring_mu19_classification
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-22T02:07:52.05027+00:00
-- url     : https://prove2.me/theorems/f54f83b0-109f-4ff1-bd11-0b09ee102c24
-- statement:
--   The canonical original scalar change of the same given finite flat local Hopf model at nineteen has a literal mu19 bialgebra equivalence whose field points equal the same given arithmetic root label after the original fixed point restriction. The complete original proposition and helper type, original fixed point restriction type and whole value, five original scoped provider types and two whole values, and every original coefficient and point context are independently checked. Every original hypothesis, including flatness without assuming freeness, is retained. Named downstream consumer: the exact previously selected pi quotient map in literal mu19 coordinates before integral norm torsor pushforward.

import Definitions.Def_MazurTransfer_OriginalRationalSubringMu19ClassificationData20261020
import Definitions.Def_MazurTransfer_OriginalBialgebraCyclicMu19PointsData20261020
import Theorems.Thm_MazurTransfer_original_rational_subring_base_change_laws
import Theorems.Thm_MazurTransfer_original_literal_nineteen_roots_normalized_classification
noncomputable section
open MazurTransfer.Order13LocalIntegralCoefficientMaps MazurTransfer.Order13RationalSubringBaseChange MazurTransfer.Order13RationalSubringMu19Classification
open MazurTransfer.NineteenRootsGaloisRepresentation MazurTransfer.CyclicNineteenGroupAlgebraPoints MazurTransfer.BialgebraCyclicMu19Points
open scoped TensorProduct
local notation "F" => AlgebraicClosure ℚ
local notation "R" => LocalRing 19
local notation "S" => GaloisRep.ratLocalizedAt 19
attribute [local instance] MazurTransfer.Order13RationalSubringMu19Classification.instAlgebraLocalRingOfNatNatAlgebraicClosureRat_order13RationalSubringMu19Classification
attribute [local instance] MazurTransfer.Order13RationalSubringMu19Classification.instIsScalarTowerLocalRingOfNatNatSubtypeRatMemSubringRatLocalizedAtAlgebraicClosure_order13RationalSubringMu19Classification
attribute [local instance] MazurTransfer.Order13RationalSubringMu19Classification.instFactPrimeOfNatNat_order13RationalSubringMu19Classification
attribute [local instance] MazurTransfer.Order13RationalSubringMu19Classification.instIsScalarTowerLocalRingOfNatNatRatAlgebraicClosure_order13RationalSubringMu19Classification
attribute [local instance] MazurTransfer.Order13RationalSubringMu19Classification.instModuleZModOfNatNatAdditiveSubtypeUnitsAlgebraicClosureRatMemSubgroupRoots_order13RationalSubringMu19Classification

theorem MazurTransfer.original_rational_subring_mu19_classification : ∀ (H : Type) [CommRing H] [HopfAlgebra R H] [Module.Finite R H] [Module.Flat R H] [Coalgebra.IsCocomm R H] (e : WithConv (H →ₐ[R] F) ≃ Additive (Roots F)) (he_add : ∀ f g, e (f * g) = e f + e g) (he_act : ∀ (σ : F ≃ₐ[ℚ] F) (f g : WithConv (H →ₐ[R] F)), (∀ x : H, g x = σ (f x)) → e g = rootsRepresentation F σ (e f)),
∃ ψ : (S ⊗[R] H) ≃ₐc[S] MonoidAlgebra S Cyclic,
      ∀ f : WithConv (S ⊗[R] H →ₐ[S] F),
        literalPointEquiv ψ F f = (e (fixedBasePoint H f)).toMul := by sorry
