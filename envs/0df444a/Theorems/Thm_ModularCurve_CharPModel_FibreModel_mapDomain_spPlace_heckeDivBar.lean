-- Prove2me | Theorems.Thm_ModularCurve_CharPModel_FibreModel_mapDomain_spPlace_heckeDivBar
-- name    : ModularCurve.CharPModel.FibreModel.mapDomain_spPlace_heckeDivBar
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:12.70306+00:00
-- url     : https://prove2.me/theorems/8660c807-f28f-5956-a994-b673460318c3
-- title:
--   Eichler–Shimura congruence on all divisors, squarefree level
-- statement:
--   Fix a valuation subring $A$ of $\overline{\mathbb Q}$, a prime $\ell$ and a positive integer $N$ with $N$ squarefree and $\ell \nmid N$. Let `data` be modular polynomial data at level $\ell$, that is a monic $\Phi \in \mathbb Z[X][Y]$ of degree $\psi(\ell)$ annihilating $j(q^{\ell})$ over $j(q)$, subject to the Kronecker congruence identifying the bivariate reduction of $\Phi$ modulo $\ell$ with the product of $Y^{\ell} - X$ and $Y - X^{\ell}$; let $k$ be a field of characteristic $\ell$ and $\mathrm{red} : A \to k$ a surjective ring homomorphism. Assume the two degeneracy embeddings $\alpha,\beta$ of the base-changed function field of level $N$ into that of level $N\ell$ over $\overline{\mathbb Q}$ are integral, that principal divisors exist on the level-$N\ell$ field, and that modular polynomial data $\Phi_d$ are given for all $d \mid N$, with $\Phi_N$ satisfying `EvalSymm` (symmetry of its two-variable evaluation on Laurent series over $\mathbb Q$) and its reduction to $k$ separable over $k(X)$. Let `fm` be a fibre model of level $N$ at $(A,\mathrm{red})$, with induced specialisation map `fm.spPlace` from places of $\overline{\mathbb Q}(X_0(N))$ to places of the characteristic-$\ell$ field `modularFunctionFieldC k N`. Then for every divisor $D$ of the level-$N$ base-changed field, the pushforward along `fm.spPlace` of $\beta_*\alpha^* D$ equals $(F_* + F^*)$, as defined by `heckeFibreGeomLevel k N data hKr`, applied to the pushforward of $D$.
--
--   This is the Eichler–Shimura congruence relation in its divisor-theoretic form: the Hecke correspondence $T_\ell$ upstairs specialises to the sum of the Frobenius pushforward and pullback on the characteristic-$\ell$ fibre, for an arbitrary fibre model and at all places, including those above cusps, supersingular points and singularities of the plane model. It is used in the analysis of the degree-two part of the specialisation map, [`ModularCurve.CharPModel.FibreModel.spPlace_d2`](thm.html#ModularCurve.CharPModel.FibreModel.spPlace_d2).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_CharPModel_FibreModel_mapDomain_spPlace_heckeDivBar.lean

import Definitions.Def_ModularCurve_SpecializationMap

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open ModularCurve ModularCurve.CharPModel AlgebraicCurve Polynomial

theorem ModularCurve.CharPModel.FibreModel.mapDomain_spPlace_heckeDivBar
    (A : ValuationSubring (AlgebraicClosure ℚ)) (ℓ N : ℕ) [Fact ℓ.Prime] [NeZero N]
    (hsq : Squarefree N) (hlN : ¬ ℓ ∣ N)
    (data : ModularPolynomialData ℓ) (hKr : KroneckerCongruence ℓ data)
    (k : Type*) [Field k] [CharP k ℓ] (red : A →+* k)
    (halpha : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N ℓ)
    (hbeta : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N ℓ)
    [HasPrincipalDivisors (AlgebraicClosure ℚ)
        (laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull (N * ℓ)))]
    (hred : Function.Surjective red)
    (dataAll : ∀ (d : ℕ) [NeZero d], d ∣ N → ModularPolynomialData d)
    (hsym : EvalSymm (dataAll N (dvd_refl N)).Φ)
    (hsep : (((dataAll N (dvd_refl N)).Φ.map
        (Polynomial.mapRingHom (Int.castRingHom k))).map
      (algebraMap (Polynomial k) (RatFunc k))).Separable)
    (fm : FibreModel N A ℓ k red)
    (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) :
    Finsupp.mapDomain (fm.spPlace hred dataAll hsep) (heckeDivBar halpha hbeta D) =
      heckeFibreGeomLevel k N data hKr
        (Finsupp.mapDomain (fm.spPlace hred dataAll hsep) D) := by sorry
