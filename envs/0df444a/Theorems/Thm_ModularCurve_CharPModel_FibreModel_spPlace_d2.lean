-- Prove2me | Theorems.Thm_ModularCurve_CharPModel_FibreModel_spPlace_d2
-- name    : ModularCurve.CharPModel.FibreModel.spPlace_d2
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:12.70306+00:00
-- url     : https://prove2.me/theorems/dd87aab6-0db3-5c87-844a-99f3df8bf04d
-- title:
--   Unramified Frobenius lift for the specialisation map, clause d2
-- statement:
--   Fix a valuation subring $A$ of $\overline{\mathbb Q}$, natural numbers $\ell$ and $N$ with $\ell$ prime and $N \neq 0$, and assume $N$ squarefree and $\ell \nmid N$. Let `data` be a modular-polynomial datum of level $\ell$, i.e. a monic $\Phi \in \mathbb Z[X][Y]$ of degree $\psi(\ell)$ in $Y$ with $\Phi(j, j(q^{\ell})) = 0$ as Laurent series, and let `hKr` assert the Kronecker congruence, that the reduction of $\Phi$ modulo $\ell$ equals $(Y^{\ell} - X)(Y - X^{\ell})$ in $\mathbb F_\ell[X][Y]$. Let $k$ be a field of characteristic $\ell$ and $\mathrm{red} : A \to k$ a surjective ring homomorphism. Assume the two level-raising maps from the base-changed level-$N$ field $\bar F_N = \overline{\mathbb Q}\cdot F_N \subset \overline{\mathbb Q}((q))$ to $\bar F_{N\ell}$ are integral: the degeneracy inclusion $\alpha$ = `heckeAlphaBar` and the map $\beta$ = `heckeBetaBar` induced by $q \mapsto q^{\ell}$. Assume further given modular-polynomial data for every divisor $d \mid N$, with the level-$N$ datum $\Phi_N$ evaluation-symmetric ($\Phi_N(x,y) = \Phi_N(y,x)$ for all Laurent series $x, y$ over $\mathbb Q$) and with its image in $k(X)[Y]$ separable, and let `fm` be a fibre model of level $N$ over $(A, \mathrm{red})$, whose associated specialisation map $\mathrm{sp} =$ `fm.spPlace` sends places of $\bar F_N$ over $\overline{\mathbb Q}$ to places of the characteristic-$\ell$ field $\mathrm{modularFunctionFieldC}\ k\ N = k(j, j_N)$ (places being valuation subrings containing the constants, proper, and principal ideal rings). Write $\mathrm{Frob}$ for `frobOnPlacesGeomLevel`, the operator on places of $k(j, j_N)$ obtained by restricting along the image of the $\ell$-power $q$-expansion embedding and transporting back by the induced isomorphism. The assertion: for every place $v$ of $\bar F_N$ with $\mathrm{Frob}^2(\mathrm{sp}\,v) \neq \mathrm{sp}\,v$, there is a place $W_0$ of $\bar F_{N\ell}$ such that the restriction of $W_0$ along $\beta$ is $v$, that $\mathrm{sp}$ of the restriction of $W_0$ along $\alpha$ equals $\mathrm{Frob}(\mathrm{sp}\,v)$, that the ramification index of $W_0$ along $\beta$ is $1$, and that $W_0$ is the only place of $\bar F_{N\ell}$ with the first two of these properties.
--
--   This is the clause of the place-specialisation data for $X_0(N)$ in characteristic $\ell$ which records that, above a place whose specialisation is not fixed by $\mathrm{Frob}^2$, exactly one of the points of the $\ell$-isogeny correspondence lying over it specialises to the Frobenius image, and does so unramifiedly; it expresses the Eichler–Shimura relation $T_\ell = \mathrm{Frob} + \langle \ell \rangle \mathrm{Frob}^{\vee}$ at the level of places. It is used in the assembly of the specialisation morphism on degree-zero divisor classes, in `exists_placeSpecialization_spPic0_eq` and `exists_placeSpecialization_spPic0_eq_of_prime`.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_CharPModel_FibreModel_spPlace_d2.lean

import Definitions.Def_ModularCurve_SpecializationMap

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicCurve ModularCurve CharPModel

theorem ModularCurve.CharPModel.FibreModel.spPlace_d2
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
    (fm : FibreModel N A ℓ k red) :
    ∀ v : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N),
    frobOnPlacesGeomLevel k N data hKr
        (frobOnPlacesGeomLevel k N data hKr ((fm.spPlace hred dataAll hsep) v)) ≠ (fm.spPlace hred
            dataAll hsep) v →
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
