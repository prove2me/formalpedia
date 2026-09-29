-- Prove2me | Theorems.Thm_ModularCurve_CharPModel_FibreModel_mapDomain_spPlace_heckeDivBar_of_cuspChart_of_level
-- name    : ModularCurve.CharPModel.FibreModel.mapDomain_spPlace_heckeDivBar_of_cuspChart_of_level
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:12.70306+00:00
-- url     : https://prove2.me/theorems/910e2392-6c81-52cd-84cc-4fc815685fdf
-- title:
--   Eichler–Shimura relation for sp_* at level N prime to ℓ
-- statement:
--   Fix a valuation subring $A$ of $\overline{\mathbb Q}$, a prime $\ell$ and a nonzero $N$ with $\ell \nmid N$. Let `data` be modular polynomial data at level $\ell$, i.e. a monic $\Phi \in \mathbb Z[X][Y]$ of degree $\psi(\ell)$ annihilating $j(q^\ell)$ over $\mathbb Q(j)$, subject to Kronecker's congruence `hKr`, which says that the bivariate reduction of $\Phi$ modulo $\ell$ equals $(X^\ell - Y)(X - Y^\ell)$. Let $k$ be a field of characteristic $\ell$ and $\mathrm{red} : A \to k$ a surjective ring homomorphism. Assume the two degeneracy embeddings $\alpha$, $\beta$ of the base-changed modular function field of level $N$ over $\overline{\mathbb Q}$ into that of level $N\ell$ are integral, and that every nonzero element of the level-$N\ell$ field has a degree-zero divisor recording its orders at all places. Assume further given modular polynomial data $\Phi_d$ for every divisor $d \mid N$, with $\Phi_N$ satisfying the symmetry `EvalSymm` (its two-variable evaluation on Laurent series over $\mathbb Q$ is unchanged by swapping the arguments) and with the reduction of $\Phi_N$ modulo $\ell$, viewed as a polynomial over $k(X)$, separable. Let `fm` be a fibre model of level $N$ at $(A,\mathrm{red})$ — two subrings $B_{\mathrm{fin}}, B_\infty$ of the level-$N$ function field containing the constants from $A$, with $\bar\jmath, \bar\jmath_N \in B_{\mathrm{fin}}$ and $\bar\jmath^{-1} \in B_\infty$, each integral over the corresponding affine base ring, together with reduction homomorphisms $\pi_{\mathrm{fin}}, \pi_\infty$ onto the characteristic-$\ell$ function field $k(X_0(N))$ compatible with constants and with these coordinates — and assume the cusp chart condition `cc`: $\bar\jmath_N\,\bar\jmath^{-N} \in B_\infty$ and $\pi_\infty$ sends it to $\tilde\jmath_N\,\tilde\jmath^{-N}$. Write $\mathrm{sp}$ for the induced specialisation map on places. Then for every divisor $D$ on the level-$N$ field over $\overline{\mathbb Q}$, the pushforward of the Hecke correspondence divisor $\beta_*\alpha^* D$ along $\mathrm{sp}$ equals `heckeFibreGeomLevel`, the sum of geometric Frobenius pushforward and pullback determined by `data` and `hKr`, applied to the pushforward of $D$.
--
--   This is the Eichler–Shimura congruence relation $\mathrm{sp}_*(T_\ell D) = (F_* + F^*)(\mathrm{sp}_* D)$ in its divisor form, at arbitrary level $N$ prime to $\ell$ (no squarefreeness is assumed) for a fibre model equipped with a cusp chart. It is used for the corresponding identity stated via the specialisation homomorphism on divisor groups, and for the analysis of places of the special fibre lying under poles.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_CharPModel_FibreModel_mapDomain_spPlace_heckeDivBar_of_cuspChart_of_level.lean

import Definitions.Def_ModularCurve_SpecializationMap
import Definitions.Def_ModularCurve_FibreModelCuspChart

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open ModularCurve ModularCurve.CharPModel AlgebraicCurve Polynomial

theorem ModularCurve.CharPModel.FibreModel.mapDomain_spPlace_heckeDivBar_of_cuspChart_of_level
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
    (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) :
    Finsupp.mapDomain (fm.spPlace hred dataAll hsep) (heckeDivBar halpha hbeta D) =
      heckeFibreGeomLevel k N data hKr
        (Finsupp.mapDomain (fm.spPlace hred dataAll hsep) D) := by sorry
