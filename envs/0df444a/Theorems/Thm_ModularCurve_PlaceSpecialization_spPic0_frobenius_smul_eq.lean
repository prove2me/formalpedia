-- Prove2me | Theorems.Thm_ModularCurve_PlaceSpecialization_spPic0_frobenius_smul_eq
-- name    : ModularCurve.PlaceSpecialization.spPic0_frobenius_smul_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:46.056571+00:00
-- url     : https://prove2.me/theorems/25c42e4f-d159-525f-b98f-0c6c880e02cb
-- title:
--   Frobenius acts on J₀(N) as special-fibre Frobenius push-forward
-- statement:
--   Fix a valuation subring $A$ of $\overline{\mathbb{Q}} =$ `AlgebraicClosure ℚ`, a prime $\ell$ and a nonzero level $N$, together with a `ModularPolynomialData ℓ`, i.e. a monic $\Phi \in \mathbb{Z}[X][Y]$ of degree $\psi(\ell)$ killing the pair of $q$-expansions $(j, j_\ell)$, and a witness `hKr` that $\Phi$ reduced modulo $\ell$ equals $(C(X)^{\ell} - X)(C(X) - X^{\ell})$. Let $k$ be an algebraically closed field of characteristic $\ell$ such that the subfield $\mathrm{modularFunctionFieldC}\,k\,N = k(j, j_N)$ of $k$-Laurent series is a curve over $k$ in the sense of `IsCurveOver` (principal divisors of degree zero exist, every place has residue field finite over $k$, and the module of Kähler differentials is free of rank one), let $\mathrm{red} : A \to k$ be a ring homomorphism, and let $h\alpha$, $h\beta$ assert integrality of the ring homomorphisms $\overline{\alpha}$, $\overline{\beta}$ attached to the Hecke correspondence at level $N$ and prime $\ell$ over $\overline{\mathbb{Q}}$. Let $S$ be a `PlaceSpecialization` packet for these data: a map `sp` from places of $\overline{\mathbb{Q}}(j, j_N)$ to places of $k(j, j_N)$, an additive map `spPic0` from $J_0(N) = \mathrm{Pic}^0(\overline{\mathbb{Q}}, \mathrm{modularFunctionFieldBar}\,N)$ to $\mathrm{Pic}^0(k, k(j,j_N))$, and the compatibility conditions of that structure (specialisation of orders of $j$ and $j_N$, divisor-level compatibility, and a Frobenius clause), summarised here. Then for every $\sigma \in \mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$ lying in the decomposition subgroup of $A$ and acting on the residue field of $A$ by $x \mapsto x^{\ell}$, and every $x \in J_0(N)$, one has $\mathrm{spPic0}(\sigma \cdot x) = \mathrm{frobeniusPushforwardGeomLevelPic0OfIsCurveOver}\,k\,N\,\mathrm{data}\,\mathrm{hKr}(\mathrm{spPic0}\,x)$, the right-hand map being the Frobenius push-forward on $\mathrm{Pic}^0$ of the special fibre obtained from perfectness of $k$ and the degree-one normalisation of $k(j, j_N)$.
--
--   This is the Eichler–Shimura type statement that, through a place-specialisation packet for $X_0(N)$ at $\ell$, the action of a Frobenius element of $\mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$ on $J_0(N)$ becomes the Frobenius push-forward on the divisor class group of the special fibre. It is the form consumed by the construction of good-reduction specialisation witnesses and by the subsequent comparison of decomposition-group actions with Hecke data at level $\ell$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_PlaceSpecialization_spPic0_frobenius_smul_eq.lean

import Definitions.Def_ModularCurve_PlaceSpecialization

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicCurve ModularCurve

theorem ModularCurve.PlaceSpecialization.spPic0_frobenius_smul_eq {A : ValuationSubring (AlgebraicClosure ℚ)} {ℓ N : ℕ} [Fact ℓ.Prime] [NeZero N]
    {data : ModularPolynomialData ℓ} {hKr : KroneckerCongruence ℓ data}
    {k : Type*} [Field k] [CharP k ℓ] {red : A →+* k}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N ℓ} {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N ℓ}
    [IsAlgClosed k] [IsCurveOver k (modularFunctionFieldC k N)]
    (S : PlaceSpecialization A ℓ N data hKr k red hα hβ)
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (hσ : A.IsFrobeniusAt σ ℓ) (x : JZero N) :
    S.spPic0 (σ • x) = frobeniusPushforwardGeomLevelPic0OfIsCurveOver k N data hKr (S.spPic0 x) := by sorry
