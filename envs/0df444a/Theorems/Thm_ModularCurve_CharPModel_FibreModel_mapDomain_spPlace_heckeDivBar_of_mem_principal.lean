-- Prove2me | Theorems.Thm_ModularCurve_CharPModel_FibreModel_mapDomain_spPlace_heckeDivBar_of_mem_principal
-- name    : ModularCurve.CharPModel.FibreModel.mapDomain_spPlace_heckeDivBar_of_mem_principal
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:12.70306+00:00
-- url     : https://prove2.me/theorems/e321bfd1-64e1-5a70-a709-3675f136e5f8
-- title:
--   Eichler–Shimura relation on specialised principal divisors
-- statement:
--   Fix a valuation subring $A$ of $\overline{\mathbb{Q}}$, a prime $\ell$ and a nonzero squarefree $N$ with $\ell\nmid N$. Let `data` be a modular-polynomial datum at level $\ell$ (a monic $\Phi_\ell\in\mathbb{Z}[X][Y]$ of degree $\psi(\ell)$ vanishing on the pair $(j,j_\ell)$ of $q$-expansions) satisfying the Kronecker congruence: modulo $\ell$, $\Phi_\ell$ equals $(C X^{\ell}-X)(C X-X^{\ell})$. Let $k$ be a field of characteristic $\ell$ and $\mathrm{red}:A\to k$ a surjective ring homomorphism. Assume the two degeneracy embeddings of the base-changed modular function field of level $N$ into that of level $N\ell$ have integral underlying ring maps (`HeckeAlphaBarIntegral`, `HeckeBetaBarIntegral`), and that every nonzero element of the level-$N\ell$ field has a degree-zero divisor recording its orders at all places. Assume further modular-polynomial data for every divisor of $N$, with $\Phi_N$ symmetric under interchanging its two Laurent-series arguments and with separable image in $\mathrm{RatFunc}\,k$, and let `fm` be a fibre model of level $N$ over $(A,\mathrm{red})$, giving the specialisation map $\mathrm{sp}$ from places of $\overline{\mathbb{Q}}F_N$ to places of the characteristic-$\ell$ function field `modularFunctionFieldC k N`. Then for every divisor $D$ of $\overline{\mathbb{Q}}F_N$ that is principal, i.e. $D(v)=v.\mathrm{ord}(f)$ for some $f\neq 0$, transporting $\mathrm{heckeDivBar}\,D$ (pushforward along $\alpha$ of the pullback along $\beta$) along $\mathrm{sp}$ gives the same divisor as applying $\mathrm{frobeniusPushforwardGeomLevel}+\mathrm{frobeniusPullbackGeomLevel}$ to the transport of $D$.
--
--   This is the Eichler–Shimura congruence relation $\widetilde{T_\ell}=F+V$ for $X_0(N)$ in characteristic $\ell$, here in divisor-theoretic form and restricted to the subgroup of principal divisors. It is the inductive input to [`ModularCurve.CharPModel.FibreModel.mapDomain_spPlace_heckeDivBar`](thm.html#ModularCurve.CharPModel.FibreModel.mapDomain_spPlace_heckeDivBar), where the same intertwining is established for arbitrary divisors.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_CharPModel_FibreModel_mapDomain_spPlace_heckeDivBar_of_mem_principal.lean

import Definitions.Def_ModularCurve_SpecializationMap

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open ModularCurve ModularCurve.CharPModel AlgebraicCurve Polynomial

theorem ModularCurve.CharPModel.FibreModel.mapDomain_spPlace_heckeDivBar_of_mem_principal
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
    (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N))
    (hD : D ∈ Divisor.principal (K := AlgebraicClosure ℚ) (F := modularFunctionFieldBar N)) :
    Finsupp.mapDomain (fm.spPlace hred dataAll hsep) (heckeDivBar halpha hbeta D) =
      heckeFibreGeomLevel k N data hKr
        (Finsupp.mapDomain (fm.spPlace hred dataAll hsep) D) := by sorry
