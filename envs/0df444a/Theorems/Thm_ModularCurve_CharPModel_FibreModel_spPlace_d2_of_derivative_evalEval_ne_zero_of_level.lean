-- Prove2me | Theorems.Thm_ModularCurve_CharPModel_FibreModel_spPlace_d2_of_derivative_evalEval_ne_zero_of_level
-- name    : ModularCurve.CharPModel.FibreModel.spPlace_d2_of_derivative_evalEval_ne_zero_of_level
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:12.70306+00:00
-- url     : https://prove2.me/theorems/fe1a804f-768f-5e02-9491-1e2a64df703e
-- title:
--   Unique unramified β-lift above a smooth point of the reduced model
-- statement:
--   Fix a valuation subring $A$ of $\overline{\mathbb{Q}}$, a prime $\ell$ and a level $N \neq 0$ with $\ell \nmid N$. Let `data` be a modular polynomial datum at level $\ell$, i.e. a monic $\Phi \in \mathbb{Z}[X][Y]$ of degree $\psi(\ell)$ annihilating the pair $(j, j_\ell)$ of $q$-expansions, and assume the Kronecker congruence $\Phi \equiv (C X^{\ell} - X)(C X - X^{\ell}) \pmod \ell$. Let $k$ be a field of characteristic $\ell$ and $red : A \to k$ a surjective ring homomorphism, let both degeneracy embeddings $\alpha, \beta$ from the level-$N$ to the level-$N\ell$ Laurent-series function field over $\overline{\mathbb{Q}}$ be integral, let `dataAll` assign a modular polynomial datum to every nonzero divisor $d \mid N$, assume the level-$N$ polynomial $\Phi_N$ satisfies `EvalSymm` (its two-variable evaluation on Laurent series is symmetric) and that its reduction to $k[X][Y]$, viewed over $\mathrm{RatFunc}\,k$, is separable, and let `fm` be a fibre model of the reduction at level $N$ (subrings $B_{\mathrm{fin}}, B_{\mathrm{inf}}$ of the level-$N$ field over $\overline{\mathbb{Q}}$ containing the constants $A$ together with $\bar j, \bar j_N$, respectively $\bar j^{-1}$, integral over the corresponding affine base rings, equipped with ring maps to the level-$N$ function field $k(j, j_N)$ over $k$ inducing $red$ on constants and matching the $q$-expansions $j, j_N$ in characteristic $\ell$). Let $v$ be a place of the level-$N$ field over $\overline{\mathbb{Q}}$, write $\mathrm{sp}(v)$ for its specialisation `fm.spPlace` and $\mathrm{Frob}$ for `frobOnPlacesGeomLevel`, the transport of places along the $\ell$-power $q$-expansion embedding of $k(j, j_N)$; assume $\mathrm{Frob}(\mathrm{Frob}(\mathrm{sp}(v))) \neq \mathrm{sp}(v)$. Let $s, t \in k$ be such that $\mathrm{sp}(v)$ has positive order on $j - s$ and on $j_N - t$, and assume that the reduced $\Phi_N$ is smooth at this point, in the sense that the derivative of its reduction has nonzero `evalEval` at $(s,t)$, or the derivative of the reduction of `swapBivar` $\Phi_N$ has nonzero `evalEval` at $(t,s)$. Then there is a place $W_0$ of the level-$N\ell$ field over $\overline{\mathbb{Q}}$ whose restriction along $\beta$ is $v$, whose $\alpha$-restriction specialises to $\mathrm{Frob}(\mathrm{sp}(v))$, whose ramification index along $\beta$ equals $1$, and which is the unique place with the first two of these properties.
--
--   This is the smooth-point case of the Eichler–Shimura congruence relation in the form used here: above a place whose specialisation lands at a smooth finite point of the reduced plane model of $X_0(N)$, exactly one $\beta$-lift has $\alpha$-restriction specialising to the Frobenius image, and it is unramified. It feeds the construction of place specialisations with a prescribed Frobenius-compatible prolongation tuple at level $N\ell$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_CharPModel_FibreModel_spPlace_d2_of_derivative_evalEval_ne_zero_of_level.lean

import Definitions.Def_ModularCurve_SpecializationMap
import Mathlib.Algebra.Polynomial.Bivariate

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open ModularCurve ModularCurve.CharPModel AlgebraicCurve Polynomial

theorem ModularCurve.CharPModel.FibreModel.spPlace_d2_of_derivative_evalEval_ne_zero_of_level
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
    (hsmooth : (Polynomial.derivative
        ((dataAll N (dvd_refl N)).Φ.map (Polynomial.mapRingHom (Int.castRingHom k)))).evalEval s t
        ≠ 0 ∨
      (Polynomial.derivative
        ((swapBivar (dataAll N (dvd_refl N)).Φ).map
          (Polynomial.mapRingHom (Int.castRingHom k)))).evalEval t s ≠ 0) :
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
