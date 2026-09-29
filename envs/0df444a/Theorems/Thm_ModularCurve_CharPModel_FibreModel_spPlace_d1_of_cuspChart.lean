-- Prove2me | Theorems.Thm_ModularCurve_CharPModel_FibreModel_spPlace_d1_of_cuspChart
-- name    : ModularCurve.CharPModel.FibreModel.spPlace_d1_of_cuspChart
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:12.70306+00:00
-- url     : https://prove2.me/theorems/f94f79d9-0f8f-5dba-98ee-4f727a969fed
-- title:
--   Eichler–Shimura relation at specialised places of X₀(N)
-- statement:
--   Fix a valuation subring $A$ of $\overline{\mathbb Q}$, a prime $\ell$ and a nonzero natural number $N$ with $N$ squarefree and $\ell \nmid N$. Let `data` be a modular-polynomial datum at level $\ell$, i.e. a monic $\Phi \in \mathbb Z[X][Y]$ of degree $\psi(\ell)$ vanishing at $(j, j_\ell)$, and let `hKr` assert the Kronecker congruence $\mathrm{reduceModBivar}\,\ell\,\Phi = (C X^{\ell} - X)(C X - X^{\ell})$. Let $k$ be a field of characteristic $\ell$ and $\mathrm{red} : A \to k$ a surjective ring homomorphism. Assume that the two degeneracy embeddings $\alpha =$ `heckeAlphaBar` and $\beta =$ `heckeBetaBar` of the Laurent base change over $\overline{\mathbb Q}$ of $F^{\mathrm{full}}_N$ into that of $F^{\mathrm{full}}_{N\ell}$ are integral ring maps, and let `dataAll` provide modular-polynomial data $\Phi_d$ for every $d \mid N$, with $\Phi_N$ evaluation-symmetric in the sense of `EvalSymm` and with the image of $\Phi_N$ in $\mathrm{RatFunc}(k)[Y]$, obtained by reducing coefficients modulo $\ell$, separable. Let $fm$ be a fibre model of level $N$ at $(A, \mathrm{red})$ over $k$, and assume the cusp-chart conditions $cc$: $\bar j_N \cdot \bar j^{-N}$ lies in the subring $\mathrm{BInf}$ of $fm$ and $\pi_{\infty}$ sends it to $j_{q,N} \cdot j_q^{-N}$ in $F_N$ over $k$. Write $\mathrm{sp} = fm.\mathrm{spPlace}$ for the resulting map from places of the level-$N$ Laurent base change over $\overline{\mathbb Q}$ to places of $F_N$ over $k$, and $\mathrm{Frob} =$ `frobOnPlacesGeomLevel k N data hKr` for the transport of places along the geometric-level Frobenius isomorphism supplied by the Kronecker congruence. Then for every place $W$ of the Laurent base change over $\overline{\mathbb Q}$ of $F^{\mathrm{full}}_{N\ell}$, writing $W|_\alpha$ and $W|_\beta$ for its restrictions along $\alpha$ and $\beta$, either $\mathrm{sp}(W|_\alpha) = \mathrm{Frob}(\mathrm{sp}(W|_\beta))$ or $\mathrm{Frob}(\mathrm{sp}(W|_\alpha)) = \mathrm{sp}(W|_\beta)$.
--
--   This is the place-theoretic form of the Eichler–Shimura congruence relation $T_\ell = \mathrm{Frob} + \mathrm{Frob}^{\vee}$ for the reduction of $X_0(N)$ modulo $\ell$: the two legs of the Hecke correspondence at $\ell$, specialised to characteristic $\ell$, differ by the geometric Frobenius in one of the two directions. It is the clause of the specialisation package used by [`ModularCurve.CharPModel.FibreModel.exists_placeSpecialization_spPic0_eq`](thm.html#ModularCurve.CharPModel.FibreModel.exists_placeSpecialization_spPic0_eq) and [`ModularCurve.CharPModel.FibreModel.exists_placeSpecialization_spPic0_eq_of_prime`](thm.html#ModularCurve.CharPModel.FibreModel.exists_placeSpecialization_spPic0_eq_of_prime).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_CharPModel_FibreModel_spPlace_d1_of_cuspChart.lean

import Definitions.Def_ModularCurve_SpecializationMap
import Definitions.Def_ModularCurve_FibreModelCuspChart

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicCurve ModularCurve CharPModel

theorem ModularCurve.CharPModel.FibreModel.spPlace_d1_of_cuspChart
    (A : ValuationSubring (AlgebraicClosure ℚ)) (ℓ N : ℕ) [Fact ℓ.Prime] [NeZero N]
    (hsq : Squarefree N) (hlN : ¬ ℓ ∣ N)
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
    (fm : FibreModel N A ℓ k red) (cc : fm.CuspChart) :
    ∀ W : Place (AlgebraicClosure ℚ)
      (laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull (N * ℓ))),
    (fm.spPlace hred dataAll hsep) (W.restrictAlong (heckeAlphaBar (AlgebraicClosure ℚ) N ℓ) halpha)
        = frobOnPlacesGeomLevel k N data hKr
            ((fm.spPlace hred dataAll hsep) (W.restrictAlong (heckeBetaBar (AlgebraicClosure ℚ) N ℓ)
                hbeta))
      ∨ frobOnPlacesGeomLevel k N data hKr
            ((fm.spPlace hred dataAll hsep) (W.restrictAlong (heckeAlphaBar (AlgebraicClosure ℚ) N
                ℓ) halpha))
        = (fm.spPlace hred dataAll hsep) (W.restrictAlong (heckeBetaBar (AlgebraicClosure ℚ) N ℓ)
            hbeta) := by sorry
