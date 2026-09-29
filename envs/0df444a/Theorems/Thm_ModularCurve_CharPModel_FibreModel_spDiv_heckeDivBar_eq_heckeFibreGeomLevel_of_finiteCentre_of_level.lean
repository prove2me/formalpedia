-- Prove2me | Theorems.Thm_ModularCurve_CharPModel_FibreModel_spDiv_heckeDivBar_eq_heckeFibreGeomLevel_of_finiteCentre_of_level
-- name    : ModularCurve.CharPModel.FibreModel.spDiv_heckeDivBar_eq_heckeFibreGeomLevel_of_finiteCentre_of_level
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:12.70306+00:00
-- url     : https://prove2.me/theorems/7bc5afa2-1d39-528a-bd37-54b8f287efda
-- title:
--   Specialisation of the Hecke correspondence at finite-centre places
-- statement:
--   Fix a valuation subring $A$ of $\overline{\mathbb{Q}}$, a prime $\ell$, a nonzero level $N$ with $\ell \nmid N$, modular polynomial data `data` at level $\ell$ (a monic $\Phi \in \mathbb{Z}[X][Y]$ of degree $\psi(\ell)$ killing $(j, j_\ell)$) satisfying the Kronecker congruence $\Phi \bmod \ell = (C(X)^{\ell} - X)(C(X) - X^{\ell})$, a field $k$ of characteristic $\ell$ and a surjective ring homomorphism $\mathrm{red} : A \to k$. Assume the two degeneracy algebra maps $\alpha, \beta$ from the level-$N$ to the level-$N\ell$ base-changed Laurent function field over $\overline{\mathbb{Q}}$ are integral, and that principal divisors of degree zero exist for every nonzero element of the level-$N\ell$ field. Assume given modular polynomial data at every nonzero divisor $d \mid N$, with the level-$N$ polynomial satisfying the evaluation symmetry `EvalSymm` and becoming separable over $k(X)$ after reduction of its coefficients modulo $\ell$, and a fibre model `fm` of level $N$ over $A$ with reduction $\mathrm{red}$: two chart subrings of the level-$N$ field over $\overline{\mathbb{Q}}$, one containing the constants, $\bar j$ and $\bar j_N$, the other the constants and $\bar j^{-1}$, each integral over the corresponding affine base, together with reduction homomorphisms to $k(\tilde j, \tilde j_N) \subseteq k((q))$ compatible with $\mathrm{red}$ on constants and with the charts. Let $v$ be a place of the level-$N$ field over $\overline{\mathbb{Q}}$ (a proper valuation subring containing the constants whose ideals are principal) and let $s, t \in k$ be such that the specialised place $\mathrm{sp}(v)$ has strictly positive order at both $\tilde j - s$ and $\tilde j_N - t$, that is, $\mathrm{sp}(v)$ is centred at the finite point $(s,t)$ of the affine chart. Then the image under $\mathrm{sp}$ (pushforward of divisors along the specialisation of places) of the Hecke divisor correspondence $\alpha_* \beta^{*}[v]$ equals the characteristic-$\ell$ fibre operator applied to $[\mathrm{sp}(v)]$, namely $[\mathrm{Frob}(\mathrm{sp}(v))] + \ell\,[\mathrm{Ver}(\mathrm{sp}(v))]$.
--
--   This is the divisorial form of the Eichler–Shimura congruence relation $T_\ell \equiv \mathrm{Frob} + \ell\,\mathrm{Ver}$ on the special fibre at $\ell$, in the case of a place of the characteristic-zero modular curve whose specialisation is centred at a finite point of the $(\tilde j, \tilde j_N)$-chart; the companion case is that of places specialising to a pole of $\tilde j$. It is used in the ramification count [`ModularCurve.CharPModel.FibreModel.spPlace_d2_sum_ramification_typeOne_eq_one_of_level`](thm.html#ModularCurve.CharPModel.FibreModel.spPlace_d2_sum_ramification_typeOne_eq_one_of_level).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_CharPModel_FibreModel_spDiv_heckeDivBar_eq_heckeFibreGeomLevel_of_finiteCentre_of_level.lean

import Definitions.Def_ModularCurve_SpecializationMap
import Mathlib.Algebra.Polynomial.Bivariate

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open ModularCurve ModularCurve.CharPModel AlgebraicCurve Polynomial

set_option autoImplicit false

theorem ModularCurve.CharPModel.FibreModel.spDiv_heckeDivBar_eq_heckeFibreGeomLevel_of_finiteCentre_of_level
    (A : ValuationSubring (AlgebraicClosure ℚ)) (ℓ N : ℕ) [Fact ℓ.Prime] [NeZero N]
    (hlN : ¬ ℓ ∣ N)
    (data : ModularPolynomialData ℓ) (hKr : KroneckerCongruence ℓ data)
    (k : Type*) [Field k] [CharP k ℓ] (red : A →+* k)
    (halpha : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N ℓ)
    (hbeta : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N ℓ)
    (hred : Function.Surjective red)
    (dataAll : ∀ (d : ℕ) [NeZero d], d ∣ N → ModularPolynomialData d)
    (hsym : EvalSymm (dataAll N (dvd_refl N)).Φ)
    (hsep : (((dataAll N (dvd_refl N)).Φ.map
        (Polynomial.mapRingHom (Int.castRingHom k))).map
      (algebraMap (Polynomial k) (RatFunc k))).Separable)
    (fm : FibreModel N A ℓ k red)
    [HasPrincipalDivisors (AlgebraicClosure ℚ)
      (laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull (N * ℓ)))]
    (v : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N))
    (s t : k)
    (hs : 0 < ((fm.spPlace hred dataAll hsep) v).ord (⟨jqModC k, jqModC_mem k N⟩
      - algebraMap k (modularFunctionFieldC k N) s))
    (ht : 0 < ((fm.spPlace hred dataAll hsep) v).ord (⟨jqNModC k N, jqNModC_mem k N⟩
      - algebraMap k (modularFunctionFieldC k N) t)) :
    fm.spDiv hred dataAll hsep (heckeDivBar halpha hbeta (Finsupp.single v 1))
      = heckeFibreGeomLevel k N data hKr
          (Finsupp.single ((fm.spPlace hred dataAll hsep) v) 1) := by sorry
