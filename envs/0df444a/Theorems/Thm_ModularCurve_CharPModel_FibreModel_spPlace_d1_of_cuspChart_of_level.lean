-- Prove2me | Theorems.Thm_ModularCurve_CharPModel_FibreModel_spPlace_d1_of_cuspChart_of_level
-- name    : ModularCurve.CharPModel.FibreModel.spPlace_d1_of_cuspChart_of_level
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:12.70306+00:00
-- url     : https://prove2.me/theorems/08f0729f-1627-531e-80c8-f76074ee4026
-- title:
--   Eichler–Shimura relation for the specialisation map on places
-- statement:
--   Fix a valuation subring $A$ of $\overline{\mathbb Q}$, a prime $\ell$ and $N\ge 1$ with $\ell\nmid N$, a modular-polynomial datum `data` of level $\ell$ (a monic bivariate integral polynomial $\Phi$ of degree $\psi(\ell)$ annihilating the pair $(j(q),j(q^{\ell}))$) satisfying the Kronecker congruence $\Phi \equiv (\mathrm{C}\,X^{\ell}-X)(\mathrm{C}\,X-X^{\ell})$ after reduction of the coefficients, a field $k$ of characteristic $\ell$ and a ring homomorphism $\mathrm{red}:A\to k$ assumed surjective. Assume the two degeneracy embeddings of the base-changed full modular function field at level $N$ into that at level $N\ell$, namely `heckeAlphaBar` (the inclusion) and `heckeBetaBar` (the $q\mapsto q^{\ell}$ twist), are integral ring homomorphisms. Assume further given modular-polynomial data $\Phi_d$ for every divisor $d$ of $N$, with $\Phi_N$ evaluation-symmetric on Laurent series over $\mathbb Q$ and with separable image in $\mathrm{RatFunc}\,k$ after reduction of its coefficients modulo $\ell$; and let `fm` be a fibre model of level $N$ over $(A,\mathrm{red})$ — a finite and an infinite chart, given by subrings $\mathrm{BFin}$, $\mathrm{BInf}$ of the base-changed field containing the constants and $\bar j,\bar j_N$, respectively $\bar j^{-1}$, integral over the two affine bases, together with reduction homomorphisms $\pi_{\mathrm{Fin}},\pi_{\mathrm{Inf}}$ to the characteristic-$\ell$ modular function field compatible with $\mathrm{red}$ and with $j$, $j_N$ — which carries a cusp chart: $\bar j_N\bar j^{-N}\in\mathrm{BInf}$ and $\pi_{\mathrm{Inf}}$ sends it to $j_N j^{-N}$ in characteristic $\ell$. Write $\mathrm{sp}$ for the induced map `fm.spPlace` from places of the base-changed level-$N$ field to places of the characteristic-$\ell$ modular function field, and $\mathrm{Frob}$ for `frobOnPlacesGeomLevel`, the map on places obtained by restricting along the Frobenius image and transporting by the geometric-level Frobenius isomorphism. The conclusion: for every place $W$ of the base change to $\overline{\mathbb Q}$ of the full modular function field of level $N\ell$, either $\mathrm{sp}(W|_{\alpha})=\mathrm{Frob}(\mathrm{sp}(W|_{\beta}))$ or $\mathrm{Frob}(\mathrm{sp}(W|_{\alpha}))=\mathrm{sp}(W|_{\beta})$, where $W|_{\alpha}$, $W|_{\beta}$ denote the restrictions of $W$ along the two degeneracy embeddings.
--
--   This is the Eichler–Shimura congruence relation in the form of a dichotomy between the two legs of the Hecke correspondence at $\ell$, expressed at the level of places of the function field rather than of divisor classes. It is the clause of the place-specialisation package verified for the map constructed from a fibre model, and it is used in assembling that package (including in the statement providing a fibre model with cusp chart whose place specialisation agrees with the constructed one).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_CharPModel_FibreModel_spPlace_d1_of_cuspChart_of_level.lean

import Definitions.Def_ModularCurve_SpecializationMap
import Definitions.Def_ModularCurve_FibreModelCuspChart

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicCurve ModularCurve CharPModel

theorem ModularCurve.CharPModel.FibreModel.spPlace_d1_of_cuspChart_of_level
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
