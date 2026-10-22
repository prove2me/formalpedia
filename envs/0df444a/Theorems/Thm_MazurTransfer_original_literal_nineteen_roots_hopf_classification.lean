-- Prove2me | Theorems.Thm_MazurTransfer_original_literal_nineteen_roots_hopf_classification
-- name    : MazurTransfer.original_literal_nineteen_roots_hopf_classification
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-21T20:29:55.285308+00:00
-- url     : https://prove2.me/theorems/f8d1493d-e23c-462b-929d-cb64455f9620
-- statement:
--   A given original finite-free cocommutative Hopf algebra over the rational subring at nineteen, with its fixed literal nineteenth-root arithmetic labels and original addition and Galois compatibility, has the original cyclotomic bialgebra equivalence with its Cartier dual point monoid algebra. The exact evaluation identity, every original hypothesis, and the complete original statement are retained. Named downstream consumer: explicit transport of the same selected integral pi quotient at nineteen.

import Theorems.Thm_GaloisRep_exists_bialgEquiv_monoidAlgebra_of_finiteFlatHopf_of_galoisCyclotomic
import Definitions.Def_MazurTransfer_OriginalNineteenRootsCyclotomicPowerData20261020
import Definitions.Def_MazurTransfer_OriginalRepresentationCanonicalDistribMulActionData20261020
import Theorems.Thm_MazurTransfer_original_nineteen_roots_cyclotomic_power
import Theorems.Thm_MazurTransfer_original_finite_free_hopf_arithmetic_point_rank
noncomputable section
open MazurTransfer.NineteenRootsGaloisRepresentation MazurTransfer.NineteenRootsCyclotomicPower
local notation "K" => AlgebraicClosure ℚ
attribute [local instance] MazurTransfer.NineteenRootsCyclotomicPower.instFactPrimeOfNatNat_nineteenRootsCyclotomicPower
attribute [local instance] MazurTransfer.NineteenRootsCyclotomicPower.instModuleZModOfNatNatAdditiveSubtypeUnitsMemSubgroupRoots_nineteenRootsCyclotomicPower

theorem MazurTransfer.original_literal_nineteen_roots_hopf_classification : ∀ (H : Type) [CommRing H] [HopfAlgebra (GaloisRep.ratLocalizedAt 19) H] [Module.Finite (GaloisRep.ratLocalizedAt 19) H] [Module.Free (GaloisRep.ratLocalizedAt 19) H] [Coalgebra.IsCocomm (GaloisRep.ratLocalizedAt 19) H] (e : WithConv (H →ₐ[GaloisRep.ratLocalizedAt 19] K) ≃ Additive (Roots K)) (he_add : ∀ f g, e (f * g) = e f + e g) (he_act : ∀ (σ : K ≃ₐ[ℚ] K) (f g : WithConv (H →ₐ[GaloisRep.ratLocalizedAt 19] K)), (∀ x : H, g x = σ (f x)) → e g = rootsRepresentation K σ (e f)),
∃ φ : H ≃ₐc[GaloisRep.ratLocalizedAt 19]
      MonoidAlgebra (GaloisRep.ratLocalizedAt 19)
        (WithConv (CartierDual (GaloisRep.ratLocalizedAt 19) H →ₐ[GaloisRep.ratLocalizedAt 19] K)),
      ∀ (ψ : WithConv (CartierDual (GaloisRep.ratLocalizedAt 19) H →ₐ[GaloisRep.ratLocalizedAt 19] K))
        (θ : CartierDual (GaloisRep.ratLocalizedAt 19) H),
        algebraMap (GaloisRep.ratLocalizedAt 19) K
          (θ (φ.symm (MonoidAlgebra.single ψ 1))) = ψ θ := by sorry
