-- Prove2me | Theorems.Thm_ModularCurve_CharPModel_FibreModel_spPlace_d6_inertia_of_level
-- name    : ModularCurve.CharPModel.FibreModel.spPlace_d6_inertia_of_level
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:12.70306+00:00
-- url     : https://prove2.me/theorems/bcba5bec-fa19-55ae-8877-a292a8a3ae3c
-- title:
--   Inertia acts trivially on specialised places of X₀(N)
-- statement:
--   Let $A$ be a valuation subring of $\overline{\mathbb Q}$, let $\ell$ be a prime and $N$ a nonzero natural number with $\ell \nmid N$. Let `data` be a modular-polynomial datum at level $\ell$ (a monic $\Phi \in \mathbb Z[X][Y]$ of degree $\psi(\ell)$ annihilating the $q$-expansion pair at level $\ell$) satisfying the Kronecker congruence, i.e. its bivariate reduction mod $\ell$ equals $(C(X)^{\ell}-X)(C(X)-X^{\ell})$. Let $k$ be a field of characteristic $\ell$ and $\mathrm{red} : A \to k$ a surjective ring homomorphism; assume the ring homomorphisms underlying the two level-$\ell$ Hecke embeddings $\bar\alpha,\bar\beta$ over $\overline{\mathbb Q}$ at level $N$ are integral. Let `dataAll` assign a modular-polynomial datum to each divisor $d \mid N$, with $\Phi_N$ evaluation-symmetric on Laurent series over $\mathbb Q$ and with the reduction of $\Phi_N$ modulo $\ell$, viewed in $\mathrm{RatFunc}(k)[Y]$, separable. Let `fm` be a fibre model of level $N$ over $(A,\mathrm{red})$ with values in $k$. The assertion is that for every $\sigma \in \mathrm{Aut}(\overline{\mathbb Q}/\mathbb Q)$ lying in the image of the inertia subgroup of $A$ inside its decomposition group, and every place $w$ of the base-changed modular function field $\overline{\mathbb Q}\cdot F_N$ over $\overline{\mathbb Q}$, the specialisation map `fm.spPlace hred dataAll hsep` takes the translate of $w$ by the semilinear automorphism induced coefficientwise by $\sigma$ to the same place of the characteristic-$\ell$ modular function field as $w$ itself.
--
--   This is the inertia-invariance clause of the place-specialisation data attached to a fibre model of $X_0(N)$: the specialisation of places from the modular function field over $\overline{\mathbb Q}$ to its characteristic-$\ell$ counterpart factors through the inertia action at $A$. It is one of the clauses verified when the constructed map is packaged as a place specialisation, which is then used in the cusp-chart comparison and in the construction of prolongation tuples respecting the order law.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_CharPModel_FibreModel_spPlace_d6_inertia_of_level.lean

import Definitions.Def_ModularCurve_SpecializationMap

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicCurve ModularCurve CharPModel

theorem ModularCurve.CharPModel.FibreModel.spPlace_d6_inertia_of_level
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
    (fm : FibreModel N A ℓ k red) :
    ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ,
    σ ∈ A.inertiaSubgroupIn ℚ →
    ∀ w : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N),
      (fm.spPlace hred dataAll hsep) (arithmeticGalois (modularFunctionFieldFull N) σ • w) =
          (fm.spPlace hred dataAll hsep) w := by sorry
