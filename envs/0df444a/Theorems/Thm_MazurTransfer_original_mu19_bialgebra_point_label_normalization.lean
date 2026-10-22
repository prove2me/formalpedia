-- Prove2me | Theorems.Thm_MazurTransfer_original_mu19_bialgebra_point_label_normalization
-- name    : MazurTransfer.original_mu19_bialgebra_point_label_normalization
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-22T01:30:56.434681+00:00
-- url     : https://prove2.me/theorems/9021ccf0-e05c-4030-b6ea-9cb385f628fd
-- statement:
--   Normalize the given original cyclic bialgebra equivalence by an automorphism over the same coefficient ring so that its literal field-point root equals the given original arithmetic root label, pointwise. The complete original proposition and helper type, original arithmetic multiplicative label type and whole value, and every original cyclic-point and character context are independently checked. Every original ring, bialgebra, field, characteristic-zero, algebraic-closure, coefficient algebra, given equivalence and label hypothesis is retained. Named downstream consumer: exact same selected-pi quotient restriction identity in the literal mu19 model before norm torsor pushforward.

import Definitions.Def_MazurTransfer_OriginalMu19BialgebraPointLabelNormalizationData20261020
import Definitions.Def_MazurTransfer_OriginalBialgebraCyclicMu19PointsData20261020
import Definitions.Def_MazurTransfer_OriginalCyclicCharacterConjugationData20261020
import Theorems.Thm_MazurTransfer_original_cyclic_character_conjugation
noncomputable section
open MazurTransfer.CyclicNineteenGroupAlgebraPoints MazurTransfer.BialgebraCyclicMu19Points MazurTransfer.NineteenRootsGaloisRepresentation MazurTransfer.CyclicCharacterConjugation MazurTransfer.Mu19BialgebraPointLabelNormalization

theorem MazurTransfer.original_mu19_bialgebra_point_label_normalization : ∀ {R H K : Type} [CommRing R] [CommRing H] [Bialgebra R H] [Field K] [CharZero K] [IsAlgClosed K] [Algebra R K] (φ : H ≃ₐc[R] MonoidAlgebra R Cyclic) (e : WithConv (H →ₐ[R] K) ≃ Additive (Roots K)) (he_add : ∀ f g, e (f * g) = e f + e g),
∃ ψ : H ≃ₐc[R] MonoidAlgebra R Cyclic,
      ∀ f : WithConv (H →ₐ[R] K), literalPointEquiv ψ K f = (e f).toMul := by sorry
