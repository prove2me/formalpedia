-- Prove2me | Theorems.Thm_ModularCurve_PlaceSpecialization_spPic0_eq_of_sp_eq
-- name    : ModularCurve.PlaceSpecialization.spPic0_eq_of_sp_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:46.056571+00:00
-- url     : https://prove2.me/theorems/b80f4586-d86c-5961-8255-67f3f72d6da6
-- title:
--   Class-level map determined by the place-level map
-- statement:
--   Fix a valuation subring $A$ of $\overline{\mathbb{Q}}$ (realised as `AlgebraicClosure ℚ`), natural numbers $\ell$, $N$ with $\ell$ prime and $N \neq 0$, a datum `data : ModularPolynomialData ℓ`, that is a monic $\Phi \in \mathbb{Z}[X][Y]$ of degree $\psi(\ell)$ annihilating the pair $(j(q), j(q^{\ell}))$, together with a proof `hKr` of the Kronecker congruence, namely that the coefficientwise reduction of $\Phi$ modulo $\ell$ equals $(C(X)^{\ell} - X)(C(X) - X^{\ell})$ in $(\mathbb{Z}/\ell)[X][Y]$; fix also a field $k$ of characteristic $\ell$, a ring homomorphism $\mathrm{red} : A \to k$, and proofs $h\alpha$, $h\beta$ that the two Hecke base-change maps `heckeAlphaBar` and `heckeBetaBar` from the Laurent base change of the full modular function field of level $N$ to that of level $N\ell$ are integral ring homomorphisms. Let $S$ and $T$ be two place-specialization packets for these data: each consists of a map `sp` from places of $\overline{\mathbb{Q}}(X(N))$ to places of the characteristic-$\ell$ function field `modularFunctionFieldC k N`, an additive homomorphism `spPic0` from `JZero N` to $\mathrm{Pic}^0$ of that field, and axioms constraining the orders of $j$, $j_N$ and related functions at specialised places together with a compatibility field relating `spPic0` to `sp` on divisors. The assertion: if $S.\mathrm{sp} = T.\mathrm{sp}$, then $S.\mathrm{spPic0} = T.\mathrm{spPic0}$.
--
--   The statement is a uniqueness statement for the specialization map on degree-zero divisor classes of a modular curve at a prime above $\ell$, the class-level analogue of the reduction of the Jacobian at a prime of good reduction: the map on classes is pinned down by the map on places. It is used by [`ModularCurve.PlaceSpecialization.eq_of_genusFF_pos`](thm.html#ModularCurve.PlaceSpecialization.eq_of_genusFF_pos) and [`ModularCurve.PlaceSpecialization.eq_of_isModel_of_orderLawFixed`](thm.html#ModularCurve.PlaceSpecialization.eq_of_isModel_of_orderLawFixed), which deduce equality of whole place-specialization packets from agreement of their place-level data.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_PlaceSpecialization_spPic0_eq_of_sp_eq.lean

import Definitions.Def_ModularCurve_PlaceSpecialization

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicCurve ModularCurve

theorem ModularCurve.PlaceSpecialization.spPic0_eq_of_sp_eq {A : ValuationSubring (AlgebraicClosure ℚ)} {ℓ N : ℕ} [Fact ℓ.Prime] [NeZero N]
    {data : ModularPolynomialData ℓ} {hKr : KroneckerCongruence ℓ data}
    {k : Type*} [Field k] [CharP k ℓ] {red : A →+* k}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N ℓ} {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N ℓ}
    (S T : PlaceSpecialization A ℓ N data hKr k red hα hβ) (h : S.sp = T.sp) :
    S.spPic0 = T.spPic0 := by sorry
