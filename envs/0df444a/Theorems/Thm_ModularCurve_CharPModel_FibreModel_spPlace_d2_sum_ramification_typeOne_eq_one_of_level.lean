-- Prove2me | Theorems.Thm_ModularCurve_CharPModel_FibreModel_spPlace_d2_sum_ramification_typeOne_eq_one_of_level
-- name    : ModularCurve.CharPModel.FibreModel.spPlace_d2_sum_ramification_typeOne_eq_one_of_level
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:12.70306+00:00
-- url     : https://prove2.me/theorems/2e863c09-9a62-5ca7-8732-f96f76cf57ef
-- title:
--   Type-one β-ramification sum equals one at nodal points
-- statement:
--   Fix a valuation subring $A$ of $\overline{\mathbb Q}$, a prime $\ell$ and a level $N$ with $\ell \nmid N$; a datum `data : ModularPolynomialData ℓ` (a monic bivariate integral polynomial $\Phi$ of degree $\psi(\ell)$ vanishing on $(j, j_\ell)$) satisfying the Kronecker congruence $\Phi \equiv (X'^{\,\ell}-X)(X'-X^{\ell}) \bmod \ell$; a field $k$ of characteristic $\ell$ and a surjective ring homomorphism $\mathrm{red} : A \to k$; integrality hypotheses `halpha`, `hbeta` for the two maps $\alpha$ (inclusion) and $\beta$ ($q \mapsto q^{\ell}$) from the base-changed level-$N$ function field over $\overline{\mathbb Q}$ into the level-$N\ell$ one, together with the existence of principal divisors at level $N\ell$; data `dataAll` for every divisor of $N$, with $\Phi_N$ evaluation-symmetric and with separable reduction over $k(X)$; and a fibre model $fm$ of level $N$ over $A$ reducing to $k$ (two subrings of the base-changed function field, containing the constants and $j, j_N$ respectively $j^{-1}$, integral over the corresponding affine bases, with reduction homomorphisms to $\mathrm{modularFunctionFieldC}\ k\ N$ compatible with $\mathrm{red}$, $j$, $j_N$ and $j^{-1}$), giving the specialisation map $\mathrm{sp} = fm.\mathrm{spPlace}$. Let $v$ be a place of the base-changed level-$N$ field such that the geometric-level Frobenius $\mathrm{Frob}$ satisfies $\mathrm{Frob}^2(\mathrm{sp}(v)) \ne \mathrm{sp}(v)$, and let $s,t \in k$ be such that $j - s$ and $j_N - t$ both have positive order at $\mathrm{sp}(v)$, while both partial derivatives of the mod-$\ell$ reduction of $\Phi_N$ vanish at $(s,t)$. Then the sum of the $\beta$-ramification indices of those places $W$ above $v$ along $\beta$ whose $\alpha$-restriction specialises to $\mathrm{Frob}(\mathrm{sp}(v))$ equals $1$ in $\mathbb Z$.
--
--   This is the divisor-theoretic form of the type-one part of the Eichler–Shimura relation $T_\ell = \mathrm{Frob} + \mathrm{Ver}$ at a singular (nodal) point of the reduced plane model of $X_0(N)$: the total $\beta$-ramification of the lifts of $v$ sitting over the Frobenius branch is exactly one. It is used in the companion statement [`ModularCurve.CharPModel.FibreModel.spPlace_d2_of_derivative_evalEval_eq_zero_of_level`](thm.html#ModularCurve.CharPModel.FibreModel.spPlace_d2_of_derivative_evalEval_eq_zero_of_level), which extracts from this count the existence and uniqueness of an unramified lift at such a point.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_CharPModel_FibreModel_spPlace_d2_sum_ramification_typeOne_eq_one_of_level.lean

import Definitions.Def_ModularCurve_SpecializationMap
import Mathlib.Algebra.Polynomial.Bivariate

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open ModularCurve ModularCurve.CharPModel AlgebraicCurve Polynomial

theorem ModularCurve.CharPModel.FibreModel.spPlace_d2_sum_ramification_typeOne_eq_one_of_level
    (A : ValuationSubring (AlgebraicClosure ℚ)) (ℓ N : ℕ) [Fact ℓ.Prime] [NeZero N]
    (hlN : ¬ ℓ ∣ N)
    (data : ModularPolynomialData ℓ) (hKr : KroneckerCongruence ℓ data)
    (k : Type*) [Field k] [CharP k ℓ] (red : A →+* k)
    (halpha : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N ℓ)
    (hbeta : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N ℓ)
    [HasPrincipalDivisors (AlgebraicClosure ℚ)
        (laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull (N * ℓ)))]
    [DecidableEq (Place k (modularFunctionFieldC k N))]
    (hred : Function.Surjective red)
    (dataAll : ∀ (d : ℕ) [NeZero d], d ∣ N → ModularPolynomialData d)
    (hsym : EvalSymm (dataAll N (dvd_refl N)).Φ)
    (hsep : (((dataAll N (dvd_refl N)).Φ.map
        (Polynomial.mapRingHom (Int.castRingHom k))).map
      (algebraMap (Polynomial k) (RatFunc k))).Separable)
    (fm : FibreModel N A ℓ k red)
    (v : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N))
    (hv : frobOnPlacesGeomLevel k N data hKr
        (frobOnPlacesGeomLevel k N data hKr ((fm.spPlace hred dataAll hsep) v)) ≠ (fm.spPlace hred
            dataAll hsep) v)
    (s t : k)
    (hs : 0 < ((fm.spPlace hred dataAll hsep) v).ord (⟨jqModC k, jqModC_mem k N⟩
      - algebraMap k (modularFunctionFieldC k N) s))
    (ht : 0 < ((fm.spPlace hred dataAll hsep) v).ord (⟨jqNModC k N, jqNModC_mem k N⟩
      - algebraMap k (modularFunctionFieldC k N) t))
    (hsingY : (Polynomial.derivative
        ((dataAll N (dvd_refl N)).Φ.map (Polynomial.mapRingHom (Int.castRingHom k)))).evalEval s t
      = 0)
    (hsingX : (Polynomial.derivative
        ((swapBivar (dataAll N (dvd_refl N)).Φ).map
          (Polynomial.mapRingHom (Int.castRingHom k)))).evalEval t s = 0) :
    ∑ W ∈ (Place.fiberAlong (heckeBetaBar (AlgebraicClosure ℚ) N ℓ) hbeta v).filter
        (fun W => (fm.spPlace hred dataAll hsep)
            (W.restrictAlong (heckeAlphaBar (AlgebraicClosure ℚ) N ℓ) halpha)
          = frobOnPlacesGeomLevel k N data hKr ((fm.spPlace hred dataAll hsep) v)),
      (W.ramificationIndexAlong (heckeBetaBar (AlgebraicClosure ℚ) N ℓ) : ℤ) = 1 := by sorry
