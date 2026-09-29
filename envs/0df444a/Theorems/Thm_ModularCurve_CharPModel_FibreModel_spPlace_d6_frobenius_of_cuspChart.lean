-- Prove2me | Theorems.Thm_ModularCurve_CharPModel_FibreModel_spPlace_d6_frobenius_of_cuspChart
-- name    : ModularCurve.CharPModel.FibreModel.spPlace_d6_frobenius_of_cuspChart
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:12.70306+00:00
-- url     : https://prove2.me/theorems/2c31c93e-6817-5fa5-8af0-76a245744705
-- title:
--   Specialisation carries arithmetic Frobenius to geometric Frobenius
-- statement:
--   Fix a valuation subring $A$ of $\overline{\mathbb Q}$, natural numbers $\ell$ and $N$ with $\ell$ prime and $N \neq 0$, and assume $N$ squarefree and $\ell \nmid N$. Let `data` be a modular polynomial datum of level $\ell$, that is a monic $\Phi \in \mathbb Z[X][Y]$ of degree $\psi(\ell)$ vanishing on the pair $(j, j_\ell)$ of $q$-expansions, and assume `hKr`, the Kronecker congruence: the reduction of $\Phi$ modulo $\ell$ equals $(X^\ell - Y)(X - Y^\ell)$ in the bivariate sense recorded by `KroneckerCongruence`. Let $k$ be a field of characteristic $\ell$ and $red : A \to k$ a surjective ring homomorphism, and assume that the two level-$\ell$ degeneracy homomorphisms on the base-changed modular function field, `heckeAlphaBar` and `heckeBetaBar`, are integral. Let `dataAll` assign to each divisor $d \mid N$ a modular polynomial datum of level $d$, with the level-$N$ polynomial evaluation-symmetric in the sense of `EvalSymm` (its two $\mathrm{eval}_2$-substitutions into Laurent series agree) and with separable image in $\mathrm{RatFunc}(k)[Y]$. Let $fm$ be a fibre model of level $N$ over $(A, red)$ in characteristic $\ell$ — subrings $B_{\mathrm{fin}}, B_{\mathrm{inf}}$ of the base-changed full modular function field over $\overline{\mathbb Q}$, containing the constants from $A$ and the relevant $j$-functions, integral over the respective affine bases, together with reduction homomorphisms $\pi_{\mathrm{fin}}, \pi_{\mathrm{inf}}$ to the characteristic-$\ell$ modular function field matching $red$ and the $j$-functions — and let $cc$ witness the cusp chart: $j_N \cdot j^{-N}$ lies in $B_{\mathrm{inf}}$ and $\pi_{\mathrm{inf}}$ sends it to the corresponding element $j_{N,k} \cdot j_k^{-N}$. Write $\mathrm{sp} = fm.\mathrm{spPlace}\ hred\ dataAll\ hsep$ for the resulting map from places of the base-changed modular function field over $\overline{\mathbb Q}$ to places of the modular function field over $k$. The assertion is: for every $\sigma \in \mathrm{Gal}(\overline{\mathbb Q}/\mathbb Q)$ which is a Frobenius at $\ell$ for $A$ (it lies in the decomposition subgroup of $A$ and acts on the residue field of $A$ by $x \mapsto x^\ell$) and every place $w$, one has $\mathrm{sp}(\mathrm{arithmeticGalois}(\sigma) \cdot w) = \mathrm{frobOnPlacesGeomLevel}(\mathrm{sp}\, w)$, where the left action is by the semilinear automorphism induced by $\sigma$ on coefficients and the right-hand side is transport of places along the $\ell$-power Frobenius of the geometric modular function field.
--
--   This is the Frobenius compatibility clause in the package of properties of the specialisation map attached to a fibre model of $X_0(N)$ at a valuation ring of $\overline{\mathbb Q}$ above $\ell$: reduction of places intertwines the arithmetic Galois action of a Frobenius element at $\ell$ with the geometric $\ell$-power Frobenius on the reduced curve, the Eichler–Shimura relation in its Kroneckerian-model form. It is used by the existence statements for a place specialisation with the prescribed divisor-class behaviour, [`ModularCurve.CharPModel.FibreModel.exists_placeSpecialization_spPic0_eq`](thm.html#ModularCurve.CharPModel.FibreModel.exists_placeSpecialization_spPic0_eq) and its prime-level variant.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_CharPModel_FibreModel_spPlace_d6_frobenius_of_cuspChart.lean

import Definitions.Def_ModularCurve_SpecializationMap
import Definitions.Def_ModularCurve_FibreModelCuspChart

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicCurve ModularCurve CharPModel

theorem ModularCurve.CharPModel.FibreModel.spPlace_d6_frobenius_of_cuspChart
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
    ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ,
    A.IsFrobeniusAt σ ℓ →
    ∀ w : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N),
      (fm.spPlace hred dataAll hsep) (arithmeticGalois (modularFunctionFieldFull N) σ • w)
        = frobOnPlacesGeomLevel k N data hKr ((fm.spPlace hred dataAll hsep) w) := by sorry
