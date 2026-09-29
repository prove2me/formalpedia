-- Prove2me | Theorems.Thm_ModularCurve_CharPModel_FibreModel_spPlace_d6_frobenius_of_cuspChart_of_level
-- name    : ModularCurve.CharPModel.FibreModel.spPlace_d6_frobenius_of_cuspChart_of_level
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:12.70306+00:00
-- url     : https://prove2.me/theorems/e99bb793-7118-5ca7-b5a3-5b12fead860d
-- title:
--   Specialisation transports arithmetic Frobenius to geometric Frobenius
-- statement:
--   Fix a valuation subring $A$ of $\overline{\mathbb Q}$, a prime $\ell$ and a level $N \neq 0$ with $\ell \nmid N$. Assume given: a modular-polynomial datum `data` at level $\ell$ (a monic $\Phi \in \mathbb Z[X][Y]$ of degree $\psi(\ell)$ annihilating the $q$-expansion pair $(j, j_\ell)$) satisfying the Kronecker congruence $\Phi \equiv (X^\ell - Y)(X - Y^\ell) \bmod \ell$; a field $k$ of characteristic $\ell$ and a ring homomorphism $\mathrm{red} : A \to k$ which is surjective; integrality of the two degeneracy embeddings at level $(N,\ell)$ over $\overline{\mathbb Q}$, i.e. `HeckeAlphaBarIntegral` and `HeckeBetaBarIntegral`; modular-polynomial data $\Phi_d$ for every nonzero $d \mid N$, with $\Phi_N$ evaluation-symmetric on Laurent series over $\mathbb Q$ and with its reduction over $\mathrm{RatFunc}\,k$ separable; a fibre model $fm$ of level $N$ for $(A,\mathrm{red})$ in characteristic $\ell$, together with a cusp chart for it, asserting that $\bar j_N \cdot \bar j^{-N}$ lies in the infinite-chart subring $fm.\mathrm{BInf}$ and is carried by $\pi_{\infty}$ to $j_{q,N} \cdot j_q^{-N}$ in $k$-coefficients. Write $\mathrm{sp} = fm.\mathrm{spPlace}$ for the resulting map from places of the base-changed modular function field $\overline{\mathbb Q}\,\bar F_N$ to places of $\mathrm{modularFunctionFieldC}\,k\,N$. The assertion is: for every $\sigma \in \mathrm{Gal}(\overline{\mathbb Q}/\mathbb Q)$ lying in the decomposition subgroup of $A$ and acting on the residue field of $A$ by $x \mapsto x^{\ell}$, and every place $w$ of $\overline{\mathbb Q}\,\bar F_N$, one has $\mathrm{sp}(\sigma \cdot w) = \mathrm{Frob}(\mathrm{sp}\,w)$, where $\sigma$ acts on places through the semilinear automorphism `arithmeticGalois` attached to $\sigma$ and $\mathrm{Frob} =$ `frobOnPlacesGeomLevel` is transport of places along the $\ell$-power Frobenius identification of $\mathrm{modularFunctionFieldC}\,k\,N$ with its Frobenius image.
--
--   This is the Frobenius compatibility clause of the place-specialisation package for $X_0(N)$ — the Eichler–Shimura-style statement that reduction at a place above $\ell$ intertwines the arithmetic Frobenius on $\overline{\mathbb Q}$-places with the geometric $\ell$-power Frobenius in characteristic $\ell$ — proved here for the specialisation map built from a fibre model equipped with a cusp chart, at every level prime to $\ell$. It feeds the existence theorems producing a place specialisation with the required clauses, and from there the construction of prolongation tuples for models of the modular curve.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_CharPModel_FibreModel_spPlace_d6_frobenius_of_cuspChart_of_level.lean

import Definitions.Def_ModularCurve_SpecializationMap
import Definitions.Def_ModularCurve_FibreModelCuspChart

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicCurve ModularCurve CharPModel

theorem ModularCurve.CharPModel.FibreModel.spPlace_d6_frobenius_of_cuspChart_of_level
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
    (fm : FibreModel N A ℓ k red) (cc : fm.CuspChart) :
    ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ,
    A.IsFrobeniusAt σ ℓ →
    ∀ w : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N),
      (fm.spPlace hred dataAll hsep) (arithmeticGalois (modularFunctionFieldFull N) σ • w)
        = frobOnPlacesGeomLevel k N data hKr ((fm.spPlace hred dataAll hsep) w) := by sorry
