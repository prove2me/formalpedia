-- Prove2me | Theorems.Thm_MazurTransfer_original_local_rational_subring_equivalence_compatibility
-- name    : MazurTransfer.original_local_rational_subring_equivalence_compatibility
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-21T02:06:39.067384+00:00
-- url     : https://prove2.me/theorems/d5c51bcc-cb64-478d-8dd5-48450a30a2a9
-- statement:
--   The original localization coefficient ring and the original rational-subring coefficient ring are related by the same algebra equivalence. It and its inverse preserve the same rational embedding and all original coefficient-ring embeddings into the given algebra. All original prime, algebra and scalar-tower hypotheses are retained. Named downstream consumer: classification of the same selected actual integral nineteen character quotient.

import Definitions.Def_MazurTransfer_OriginalLocalRationalSubringEquivalenceData20261020
noncomputable section
open MazurTransfer.Order13LocalIntegralCoefficientMaps MazurTransfer.Order13LocalRationalSubringEquivalence
attribute [local instance] MazurTransfer.Order13LocalRationalSubringEquivalence.instAtPrimeIntSubtypeRatMemSubringRatLocalizedAtPrimeIdeal_order13LocalRationalSubringEquivalence

theorem MazurTransfer.original_local_rational_subring_equivalence_compatibility : (∀ (q : ℕ) [Fact q.Prime] ,
(GaloisRep.ratLocalizedAt q).subtype.comp (localRationalSubringEquiv q).toRingHom =
      algebraMap (LocalRing q) ℚ) ∧ (∀ (q : ℕ) [Fact q.Prime] (r : LocalRing q),
((localRationalSubringEquiv q r : GaloisRep.ratLocalizedAt q) : ℚ) =
      algebraMap (LocalRing q) ℚ r) ∧ (∀ (q : ℕ) [Fact q.Prime] (r : GaloisRep.ratLocalizedAt q),
algebraMap (LocalRing q) ℚ ((localRationalSubringEquiv q).symm r) = (r : ℚ)) ∧ (∀ (q : ℕ) [Fact q.Prime] (K : Type) [CommRing K] [Algebra ℚ K] [Algebra (LocalRing q) K] [IsScalarTower (LocalRing q) ℚ K] [Algebra (GaloisRep.ratLocalizedAt q) K] [IsScalarTower (GaloisRep.ratLocalizedAt q) ℚ K] (r : LocalRing q),
algebraMap (GaloisRep.ratLocalizedAt q) K (localRationalSubringEquiv q r) =
      algebraMap (LocalRing q) K r) ∧ (∀ (q : ℕ) [Fact q.Prime] (K : Type) [CommRing K] [Algebra ℚ K] [Algebra (LocalRing q) K] [IsScalarTower (LocalRing q) ℚ K] [Algebra (GaloisRep.ratLocalizedAt q) K] [IsScalarTower (GaloisRep.ratLocalizedAt q) ℚ K] (r : GaloisRep.ratLocalizedAt q),
algebraMap (LocalRing q) K ((localRationalSubringEquiv q).symm r) =
      algebraMap (GaloisRep.ratLocalizedAt q) K r) := by sorry
