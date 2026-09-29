-- Prove2me | Theorems.Thm_ModularCurve_coeffMap_pow_char_eq_qExpand_of_frobenius
-- name    : ModularCurve.coeffMap_pow_char_eq_qExpand_of_frobenius
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:49.598281+00:00
-- url     : https://prove2.me/theorems/944c3eb5-e169-5204-8882-265b118ee72a
-- title:
--   ℓ-th powers of reduced Laurent series and t↦ t^ℓ
-- statement:
--   Let $A$ and $k$ be commutative rings, let $\ell$ be a prime and suppose $k$ has characteristic $\ell$. Let $\mathrm{red} : A \to k$ and $\tau : A \to A$ be ring homomorphisms satisfying $\mathrm{red}(\tau a)^{\ell} = \mathrm{red}(a)$ for every $a \in A$, so that $\mathrm{red}\circ\tau$ is a pointwise $\ell$-th root of $\mathrm{red}$. Here [`ModularCurve.coeffMap`](def/ModularCurve_LaurentCoeff.html#L16) sends a ring homomorphism $f$ to the ring homomorphism on Laurent series (Hahn series over $\mathbb{Z}$ with well-ordered support) obtained by applying $f$ to every coefficient, and [`ModularCurve.qExpand k ℓ`](def/ModularCurve_X0.html#L25) is the ring homomorphism on Laurent series over $k$ given by reindexing the exponents along multiplication by $\ell$ on $\mathbb{Z}$, that is, by the substitution $t \mapsto t^{\ell}$. The assertion is that for every Laurent series $x$ over $A$, applying $\tau$ and then $\mathrm{red}$ coefficientwise and raising the result to the $\ell$-th power gives the same Laurent series over $k$ as substituting $t^{\ell}$ for $t$ in the coefficientwise reduction of $x$: $\big(\mathrm{red}_*(\tau_* x)\big)^{\ell} = (\mathrm{red}_* x)(t^{\ell})$.
--
--   This is the freshman's dream for formal Laurent series in characteristic $\ell$, combined with the hypothesis that $\tau$ becomes an $\ell$-th root of unity on coefficients after reduction: raising a reduced series to the $\ell$-th power amounts to substituting $t^{\ell}$ for $t$. It is used in the analysis of Frobenius on the reduction of $q$-expansion charts at cusps of modular curves, where it supplies the Frobenius identity for the relevant place.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_coeffMap_pow_char_eq_qExpand_of_frobenius.lean

import Definitions.Def_ModularCurve_CoeffSemilinearAut

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem ModularCurve.coeffMap_pow_char_eq_qExpand_of_frobenius {A k : Type*} [CommRing A] [CommRing k]
    (ℓ : ℕ) [Fact ℓ.Prime] [CharP k ℓ] (red : A →+* k) (τ : A →+* A)
    (hτ : ∀ a : A, red (τ a) ^ ℓ = red a) (x : LaurentSeries A) :
    ModularCurve.coeffMap red (ModularCurve.coeffMap τ x) ^ ℓ
      = ModularCurve.qExpand k ℓ (ModularCurve.coeffMap red x) := by sorry
