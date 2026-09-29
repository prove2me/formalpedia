-- Prove2me | Theorems.Thm_NumberField_card_mul_factorization_discr_fixedField_eq_inertiaDeg_mul_finsum_u0
-- name    : NumberField.card_mul_factorization_discr_fixedField_eq_inertiaDeg_mul_finsum_u0
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:57.964832+00:00
-- url     : https://prove2.me/theorems/17a5c0e7-1290-537f-aa4f-78a3d359800b
-- title:
--   Discriminant of a fixed field from ramification filtrations at p
-- statement:
--   Let $F$ be a number field that is Galois over $\mathbb{Q}$, with group $G = \mathrm{Gal}(F/\mathbb{Q})$ (written `F ≃ₐ[ℚ] F`), let $H \le G$ be a subgroup, let $p$ be a prime number, and let $\mathfrak{P}$ be a maximal ideal of $\mathcal{O}_F$ whose contraction to $\mathbb{Z}$ is the ideal $p\mathbb{Z}$, i.e. a prime of $F$ above $p$. Then the product of $\#H$ with the exponent of $p$ in the factorisation of $|d_K|$, where $K = F^{H}$ is the intermediate field fixed by $H$ and $d_K$ its absolute discriminant, equals the inertia degree (residue degree) of $p\mathbb{Z}$ at $\mathfrak{P}$ times the sum, over all primes $\mathfrak{Q}$ of $\mathcal{O}_F$ above $p$ and over all $j \in \mathbb{N}$, of $\#G_j(\mathfrak{Q}) - \#\bigl(G_j(\mathfrak{Q}) \cap H\bigr)$, where $G_j(\mathfrak{Q})$ denotes the inertia subgroup of $G$ attached to the ideal $\mathfrak{Q}^{j+1}$, that is the $j$-th ramification group in lower numbering. Both inner sums are sums over the (finite) support of the summand, and the subtraction is truncated subtraction of natural numbers.
--
--   This is the $\chi = \mathbf{1}$ case of the Artin conductor–discriminant formula, applied to the permutation character $\mathrm{Ind}_H^G \mathbf{1}$ and read off at a single prime $p$, in the form in which the contributions of all primes of $F$ above $p$ are summed (the version with a single fixed $\mathfrak{P}$ fails for non-normal $H$). It feeds the computation of conductors of Artin $L$-functions used in the Langlands–Tunnell argument, and a divisibility statement for discriminants of fixed fields.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_card_mul_factorization_discr_fixedField_eq_inertiaDeg_mul_finsum_u0.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField

theorem NumberField.card_mul_factorization_discr_fixedField_eq_inertiaDeg_mul_finsum_u0
    (F : Type) [Field F] [NumberField F] [IsGalois ℚ F] (H : Subgroup (F ≃ₐ[ℚ] F))
    (p : ℕ) (hp : p.Prime) (𝔓 : Ideal (𝓞 F)) [𝔓.IsMaximal] (h𝔓 : 𝔓.under ℤ = Ideal.span {(p : ℤ)}) :
    Nat.card H * (discr ↥(IntermediateField.fixedField H)).natAbs.factorization p =
      (Ideal.span {(p : ℤ)}).inertiaDeg' 𝔓 *
        ∑ᶠ 𝔔 : (Ideal.span {(p : ℤ)}).primesOver (𝓞 F), ∑ᶠ j : ℕ,
          (Nat.card (((𝔔 : Ideal (𝓞 F)) ^ (j + 1)).inertia (F ≃ₐ[ℚ] F)) -
            Nat.card ↥((((𝔔 : Ideal (𝓞 F)) ^ (j + 1)).inertia (F ≃ₐ[ℚ] F)) ⊓ H)) := by sorry
