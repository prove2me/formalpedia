-- Prove2me | Theorems.Thm_OAI_MaximalSeshadri_BertiniIntegral_etale_generic_hyperplane_section_s01
-- name    : OAI.MaximalSeshadri.BertiniIntegral.etale_generic_hyperplane_section_s01
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-10T14:44:29.500628+00:00
-- url     : https://prove2.me/theorems/f43194a0-a592-4b06-90ab-5845592caec6
-- title:
--   OAI.MaximalSeshadri.BertiniIntegral.etale_generic_hyperplane_section_s01: intermediate lemma from OpenAI, Maximal Seshadri constants on arbitrary polarized surfaces (result family 039)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MaximalSeshadri.Geometry.maximalSeshadriConstants`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Maximal Seshadri constants on arbitrary polarized surfaces (result family 039)*, OpenAI Math Release, September 23, 2026, result family 39, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.MaximalSeshadri.BertiniIntegral.etale_generic_hyperplane_section` of [lean/OAI/AlgebraicGeometry/Seshadri/Bertini/SimultaneousHyperplanes.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/AlgebraicGeometry/Seshadri/Bertini/SimultaneousHyperplanes.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MaximalSeshadri.BertiniIntegral`, with `open Polynomial`, `open scoped TensorProduct`):
--
--   ```lean
--   theorem etale_generic_hyperplane_section_s01 {K A ι : Type} {n : ℕ} [Field K] [CharZero K]
--       [IsAlgClosed K] [Uncountable K] [CommRing A] [IsDomain A]
--       [Algebra K A] [Algebra.FiniteType K A]
--       [Algebra (MvPolynomial ι K) A] [IsScalarTower K (MvPolynomial ι K) A]
--       [Algebra.Etale (MvPolynomial ι K) A]
--       (v : Fin n → A) (i j : Fin n) (a b : ι) (hab : a ≠ b)
--       (hvi : v i = algebraMap (MvPolynomial ι K) A (MvPolynomial.X a))
--       (hvj : v j = algebraMap (MvPolynomial ι K) A (MvPolynomial.X b)) (c : Set K) (hc : c.Countable) :
--       ∃ (S : Subfield K), Countable S ∧ c ⊆ S ∧
--         ∀ f : (MvPolynomial (Fin n) S)[X] →ₐ[S] K, Function.Injective f →
--           IsDomain (A ⧸ Ideal.span {algebraMap K A (f X) -
--             ∑ k, algebraMap K A (f (C (MvPolynomial.X k))) * v k})
--   ```
--
--   **Used by.** The proofs of `OAI.MaximalSeshadri.Geometry.Surface.coprime_integral_section_s01` and `OAI.MaximalSeshadri.Projective.doublePointQuartics_bertini_s01` of this split import it.
-- source:
--   OpenAI, Maximal Seshadri constants on arbitrary polarized surfaces (result family 039), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 39; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Maximal-Seshadri-Constants-on-Arbitrary-Polarized-Surfaces-September-23-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/AlgebraicGeometry/Seshadri/Bertini/SimultaneousHyperplanes.lean (declaration OAI.MaximalSeshadri.BertiniIntegral.etale_generic_hyperplane_section)

import Mathlib

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace MaximalSeshadri.BertiniIntegral
noncomputable section
open Polynomial
open scoped TensorProduct
attribute [local instance] MvPolynomial.algebraMvPolynomial
attribute [local instance] Polynomial.algebra
attribute [local instance 1100] Polynomial.algebraOfAlgebra

theorem etale_generic_hyperplane_section_s01 {K A ι : Type} {n : ℕ} [Field K] [CharZero K]
    [IsAlgClosed K] [Uncountable K] [CommRing A] [IsDomain A]
    [Algebra K A] [Algebra.FiniteType K A]
    [Algebra (MvPolynomial ι K) A] [IsScalarTower K (MvPolynomial ι K) A]
    [Algebra.Etale (MvPolynomial ι K) A]
    (v : Fin n → A) (i j : Fin n) (a b : ι) (hab : a ≠ b)
    (hvi : v i = algebraMap (MvPolynomial ι K) A (MvPolynomial.X a))
    (hvj : v j = algebraMap (MvPolynomial ι K) A (MvPolynomial.X b)) (c : Set K) (hc : c.Countable) :
    ∃ (S : Subfield K), Countable S ∧ c ⊆ S ∧
      ∀ f : (MvPolynomial (Fin n) S)[X] →ₐ[S] K, Function.Injective f →
        IsDomain (A ⧸ Ideal.span {algebraMap K A (f X) -
          ∑ k, algebraMap K A (f (C (MvPolynomial.X k))) * v k}) := by
  sorry

end
end MaximalSeshadri.BertiniIntegral

end
end

end OAI
end
