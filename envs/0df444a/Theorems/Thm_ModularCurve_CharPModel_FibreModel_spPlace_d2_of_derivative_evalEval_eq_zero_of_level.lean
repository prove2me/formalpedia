-- Prove2me | Theorems.Thm_ModularCurve_CharPModel_FibreModel_spPlace_d2_of_derivative_evalEval_eq_zero_of_level
-- name    : ModularCurve.CharPModel.FibreModel.spPlace_d2_of_derivative_evalEval_eq_zero_of_level
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:12.70306+00:00
-- url     : https://prove2.me/theorems/4beb181c-aa89-5e31-8489-c848170ea253
-- title:
--   Unique unramified β-lift above a singular point, level prime to ℓ
-- statement:
--   Fix a valuation subring $A$ of $\overline{\mathbb{Q}}$, a prime $\ell$ and a level $N \neq 0$ with $\ell \nmid N$, modular polynomial data `data` at level $\ell$ satisfying the Kronecker congruence (the reduction of its bivariate polynomial $\Phi$ modulo $\ell$ equals $(C X^{\ell} - X)(C X - X^{\ell})$), a field $k$ of characteristic $\ell$ and a surjective ring homomorphism $\mathrm{red} : A \to k$, integrality of the two degeneracy maps $\alpha$ (the inclusion of the level-$N$ into the level-$N\ell$ base-changed Laurent field over $\overline{\mathbb{Q}}$) and $\beta$ (the substitution $q \mapsto q^{\ell}$), modular polynomial data `dataAll` for every divisor of $N$ whose level-$N$ member $\Phi_N$ is evaluation-symmetric and separable after reduction to $k$ and passage to $\mathrm{RatFunc}\,k$, and a fibre model `fm` of the reduction at level $N$ over $\mathrm{red}$. Let $v$ be a place of the level-$N$ field $\overline{\mathbb{Q}}$-base-changed, write $\mathrm{sp}(v)$ for its specialisation `fm.spPlace`, and assume the geometric Frobenius on places moves $\mathrm{sp}(v)$ after two applications. Let $s, t \in k$ be such that $j - s$ and $j_N - t$ both have positive order at $\mathrm{sp}(v)$, and assume both partial derivatives of the reduction of $\Phi_N$ to $k$ vanish at $(s,t)$. Then there is a place $W_0$ of the level-$N\ell$ field with $W_0|_{\beta} = v$, with $\mathrm{sp}(W_0|_{\alpha}) = \mathrm{Frob}(\mathrm{sp}(v))$, with ramification index $1$ along $\beta$, and such that every place $W$ with $W|_{\beta} = v$ and $\mathrm{sp}(W|_{\alpha}) = \mathrm{Frob}(\mathrm{sp}(v))$ equals $W_0$.
--
--   This is the singular-point case of one clause in the Eichler–Shimura congruence relation for $X_0(N)$ in characteristic $\ell$: over a point of the reduced plane model at which both partials of the reduced modular polynomial vanish, the two coordinate values no longer separate the branches, so the unramified $\beta$-lift must be produced by a separate argument. It feeds the construction of place specialisations and prolongation data at level $N$ used downstream.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_CharPModel_FibreModel_spPlace_d2_of_derivative_evalEval_eq_zero_of_level.lean

import Definitions.Def_ModularCurve_SpecializationMap
import Mathlib.Algebra.Polynomial.Bivariate

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open ModularCurve ModularCurve.CharPModel AlgebraicCurve Polynomial

theorem ModularCurve.CharPModel.FibreModel.spPlace_d2_of_derivative_evalEval_eq_zero_of_level
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
    ∃ W₀ : Place (AlgebraicClosure ℚ)
        (laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull (N * ℓ))),
      W₀.restrictAlong (heckeBetaBar (AlgebraicClosure ℚ) N ℓ) hbeta = v
        ∧ (fm.spPlace hred dataAll hsep) (W₀.restrictAlong (heckeAlphaBar (AlgebraicClosure ℚ) N ℓ)
            halpha)
            = frobOnPlacesGeomLevel k N data hKr ((fm.spPlace hred dataAll hsep) v)
        ∧ W₀.ramificationIndexAlong (heckeBetaBar (AlgebraicClosure ℚ) N ℓ) = 1
        ∧ ∀ W : Place (AlgebraicClosure ℚ)
            (laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull (N * ℓ))),
            W.restrictAlong (heckeBetaBar (AlgebraicClosure ℚ) N ℓ) hbeta = v →
            (fm.spPlace hred dataAll hsep) (W.restrictAlong (heckeAlphaBar (AlgebraicClosure ℚ) N ℓ)
                halpha)
                = frobOnPlacesGeomLevel k N data hKr ((fm.spPlace hred dataAll hsep) v) →
              W = W₀ := by sorry
