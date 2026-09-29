-- Prove2me | Theorems.Thm_ModularCurve_PlaceSpecialization_spPic0_surjective
-- name    : ModularCurve.PlaceSpecialization.spPic0_surjective
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:46.056571+00:00
-- url     : https://prove2.me/theorems/23e642ac-6009-5a01-8711-2155ed1d3c04
-- title:
--   Surjectivity of the class map of a place-specialisation packet
-- statement:
--   Fix a valuation subring $A$ of $\overline{\mathbb{Q}} =$ `AlgebraicClosure ℚ`, a prime $\ell$ and a nonzero level $N$, a datum `data : ModularPolynomialData ℓ` (a monic $\Phi \in \mathbb{Z}[X][Y]$ of degree $\psi(\ell)$ annihilating the $q$-expansion pair for level $\ell$), together with a proof `hKr` of the Kronecker congruence for it, i.e. that the reduction of $\Phi$ modulo $\ell$ equals $(C(X)^{\ell} - X)(C(X) - X^{\ell})$ in $(\mathbb{Z}/\ell)[X][Y]$; fix further an algebraically closed field $k$ of characteristic $\ell$, a ring homomorphism $\mathrm{red} : A \to k$, and proofs $h\alpha$, $h\beta$ that the two algebra maps `heckeAlphaBar` and `heckeBetaBar` from the Laurent base change of the full modular function field of level $N$ to that of level $N\ell$ are integral ring homomorphisms. Let $S$ be a `PlaceSpecialization` packet for these data: it carries a map $S.\mathrm{sp}$ from places of $\overline{\mathbb{Q}}(\text{level } N)$, i.e. of `modularFunctionFieldBar N`, to places of `modularFunctionFieldC k N` over $k$, a group homomorphism $S.\mathrm{spPic0}$ from $\mathrm{JZero}\,N = \mathrm{Pic}^{0}$ of `modularFunctionFieldBar N` over $\overline{\mathbb{Q}}$ to $\mathrm{Pic}^{0}$ of `modularFunctionFieldC k N` over $k$, and the further compatibility fields of that structure. The conclusion is that the map $S.\mathrm{spPic0}$ is surjective.
--
--   Here $\mathrm{Pic}^{0}$ is degree-zero divisors modulo principal divisors, so $\mathrm{JZero}\,N$ plays the role of the Jacobian $J_0(N)$ in characteristic $0$ and the target that of the Jacobian of the special fibre; the statement is the surjectivity of the specialisation map on divisor classes attached to a place-specialisation packet. It is used downstream in the construction of Hecke descent families and Hecke-module structures on the special-fibre Picard group, and in the good-reduction specialisation statements for $\mathrm{JZero}\,N$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_PlaceSpecialization_spPic0_surjective.lean

import Definitions.Def_ModularCurve_PlaceSpecialization

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicCurve ModularCurve

theorem ModularCurve.PlaceSpecialization.spPic0_surjective {A : ValuationSubring (AlgebraicClosure ℚ)} {ℓ N : ℕ} [Fact ℓ.Prime] [NeZero N]
    {data : ModularPolynomialData ℓ} {hKr : KroneckerCongruence ℓ data}
    {k : Type*} [Field k] [CharP k ℓ] {red : A →+* k}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N ℓ} {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N ℓ}
    [IsAlgClosed k] (S : PlaceSpecialization A ℓ N data hKr k red hα hβ) :
    Function.Surjective S.spPic0 := by sorry
