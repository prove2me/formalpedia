-- Prove2me | Theorems.Thm_ModularCurve_CharPModel_FibreModel_mapDomain_spPlace_heckeDivBar_of_mem_principal_of_cuspChart_of_level
-- name    : ModularCurve.CharPModel.FibreModel.mapDomain_spPlace_heckeDivBar_of_mem_principal_of_cuspChart_of_level
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:12.70306+00:00
-- url     : https://prove2.me/theorems/b85f8171-7465-5940-a3a7-2338ed4d902b
-- title:
--   Eichler–Shimura relation on principal divisors, level prime to ℓ
-- statement:
--   Fix a prime $\ell$ and an integer $N \neq 0$ with $\ell \nmid N$, a valuation subring $A$ of $\overline{\mathbb{Q}}$, a field $k$ of characteristic $\ell$ and a surjective ring homomorphism $\mathrm{red} : A \to k$. Assume given: modular polynomial data at level $\ell$, that is a monic $\Phi_\ell \in \mathbb{Z}[X][Y]$ of degree $\psi(\ell)$ annihilating the pair $(j, j_\ell)$ of $q$-expansions, satisfying the Kronecker congruence $\Phi_\ell \bmod \ell = (X^\ell - Y)(X - Y^\ell)$ in the sense that `reduceModBivar` of $\Phi_\ell$ equals $(C(X)^\ell - X)(C(X) - X^\ell)$; modular polynomial data at every divisor $d \mid N$, with the level-$N$ datum $\Phi_N$ evaluation-symmetric on Laurent series and with its reduction mod $\ell$, viewed as a polynomial over $k(X)$, separable; integrality of the two degeneracy embeddings $\alpha, \beta$ of the function field of level $N$ into that of level $N\ell$ over $\overline{\mathbb{Q}}$, together with the existence of principal divisors of degree zero for the level-$N\ell$ field; and a fibre model `fm` of level $N$ at $A$ with respect to $\mathrm{red}$ (subrings $B_{\mathrm{fin}}, B_{\mathrm{inf}}$ of the function field containing the constants from $A$, with $\bar j, \bar j_N \in B_{\mathrm{fin}}$ and $\bar j^{-1} \in B_{\mathrm{inf}}$, integral over the respective affine bases, and reduction homomorphisms to the characteristic-$\ell$ function field `modularFunctionFieldC k N` compatible with $\mathrm{red}$ and with $j$, $j_N$), admitting a cusp chart, i.e. $\bar j_N \cdot \bar j^{-N} \in B_{\mathrm{inf}}$ with reduction $\tilde j_N \tilde j^{-N}$. Let $\mathrm{sp}$ be the associated specialisation map on places. Then for every divisor $D$ of `modularFunctionFieldBar N` over $\overline{\mathbb{Q}}$ that is principal, i.e. $D = \mathrm{div}(f)$ for some nonzero $f$, the pushforward along $\mathrm{sp}$ of the Hecke correspondence divisor $\alpha_*\beta^* D$ equals $(\mathrm{Frob}_* + \mathrm{Frob}^*)$ applied to the pushforward of $D$, where the right-hand operator is `heckeFibreGeomLevel`, the sum of the geometric Frobenius pushforward and pullback on divisors of `modularFunctionFieldC k N` determined by $\Phi_\ell$ and the Kronecker congruence.
--
--   This is the Eichler–Shimura congruence relation $T_\ell \equiv \mathrm{Frob}_* + \mathrm{Frob}^*$ for $X_0(N)$ with $\ell \nmid N$, proved here at the level of divisors and restricted to principal divisors, $N$ not assumed squarefree. It is the input to [`ModularCurve.CharPModel.FibreModel.mapDomain_spPlace_heckeDivBar_of_cuspChart_of_level`](thm.html#ModularCurve.CharPModel.FibreModel.mapDomain_spPlace_heckeDivBar_of_cuspChart_of_level), which removes the principality hypothesis.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_CharPModel_FibreModel_mapDomain_spPlace_heckeDivBar_of_mem_principal_of_cuspChart_of_level.lean

import Definitions.Def_ModularCurve_SpecializationMap
import Definitions.Def_ModularCurve_FibreModelCuspChart

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open ModularCurve ModularCurve.CharPModel AlgebraicCurve Polynomial

theorem ModularCurve.CharPModel.FibreModel.mapDomain_spPlace_heckeDivBar_of_mem_principal_of_cuspChart_of_level
    (A : ValuationSubring (AlgebraicClosure ℚ)) (ℓ N : ℕ) [Fact ℓ.Prime] [NeZero N]
    (hlN : ¬ ℓ ∣ N)
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
    (fm : FibreModel N A ℓ k red) (cc : fm.CuspChart)
    (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N))
    (hD : D ∈ Divisor.principal (K := AlgebraicClosure ℚ) (F := modularFunctionFieldBar N)) :
    Finsupp.mapDomain (fm.spPlace hred dataAll hsep) (heckeDivBar halpha hbeta D) =
      heckeFibreGeomLevel k N data hKr
        (Finsupp.mapDomain (fm.spPlace hred dataAll hsep) D) := by sorry
