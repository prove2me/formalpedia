-- Prove2me | Theorems.Thm_ModularCurve_CharPModel_FibreModel_exists_placeSpecialization_spPic0_eq_of_prime
-- name    : ModularCurve.CharPModel.FibreModel.exists_placeSpecialization_spPic0_eq_of_prime
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:12.70306+00:00
-- url     : https://prove2.me/theorems/6a1ae30e-3c39-5b0b-a9c9-44eb50c82721
-- title:
--   Packaging the fibre-model specialisation as a place-specialisation packet
-- statement:
--   Fix a nonzero natural number $N$ which is prime, a prime $\ell$ with $\ell \nmid N$, and a valuation subring $A$ of an algebraic closure of $\mathbb{Q}$ lying over $\ell$, in the sense that the image of $\ell$ lies in the nonunits of $A$, together with the hypothesis that the residue field of $A$ has characteristic $\ell$. Suppose given: a fibre model `fm` for level $N$ over $A$ with values in the residue field of $A$ along the residue map, i.e. a pair of subrings of the base-changed Laurent ring, one containing the constants from $A$, $\bar{j}$ and $\bar{j}_N$, the other containing the constants and $\bar{j}^{-1}$, each integral over the corresponding affine base, equipped with reduction homomorphisms into the characteristic-$\ell$ modular function field matching constants, $j$ and $j_N$; a cusp chart `cc` for `fm`, asserting that $\bar{j}_N\bar{j}^{-N}$ lies in the subring at infinity and reduces to the corresponding product of the characteristic-$\ell$ $q$-expansions; a family `dataAll` assigning to each divisor $d$ of $N$ a modular polynomial datum (a monic $\Phi \in \mathbb{Z}[X][Y]$ of degree $\psi(d)$ vanishing at $(j,j_d)$); separability of the level-$N$ polynomial $\Phi_N$ after reduction to the residue field and passage to rational functions; the hypothesis `hpres` that the divisor-level specialisation attached to `fm` carries degree-zero divisors to degree-zero divisors and principal degree-zero divisors to principal ones; squarefreeness of $N$ (implied here by primality, but assumed separately); the symmetry property `EvalSymm` for $\Phi_N$, i.e. $\Phi_N$ evaluates symmetrically in its two Laurent-series arguments over $\mathbb{Q}$; a modular polynomial datum `data` at level $\ell$ satisfying the Kronecker congruence, i.e. its bivariate reduction mod $\ell$ equals $(C X^\ell - X)(C X - X^\ell)$; and integrality of the two Hecke degeneracy homomorphisms $\bar\alpha$, $\bar\beta$ for $N$ and $\ell$ over the algebraic closure of $\mathbb{Q}$. The conclusion is that there exists a place-specialisation packet $S$ (for $A$, $\ell$, $N$, `data`, the Kronecker congruence, the residue field with the residue map, and the two integrality hypotheses), that is, a map on places together with a homomorphism $J_0(N) \to \mathrm{Pic}^0$ in characteristic $\ell$ satisfying all the packet's compatibility clauses, whose place map is `fm.spPlace` and whose Picard-group map is `fm.spPic0` for the given data.
--
--   This is the step that certifies the specialisation of $X_0(N)$ constructed from a fibre model at a place above $\ell$ as an instance of the abstract place-specialisation interface used in Mazur's specialisation argument, in the case of prime level. It is invoked in the construction of Hecke-equivariant descent families and of good-reduction specialisations of $J_0(N)$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_CharPModel_FibreModel_exists_placeSpecialization_spPic0_eq_of_prime.lean

import Definitions.Def_ModularCurve_SpecializationMap
import Definitions.Def_ModularCurve_FibreModelCuspChart
import Definitions.Def_ValuationSubring_ReduceAt

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open ModularCurve ModularCurve.CharPModel AlgebraicCurve IsLocalRing
set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 400000 in

theorem ModularCurve.CharPModel.FibreModel.exists_placeSpecialization_spPic0_eq_of_prime
    (N : ℕ) [NeZero N] (hN : N.Prime)
    (ℓ : ℕ) [hℓ : Fact ℓ.Prime] (hℓN : ¬ ℓ ∣ N)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime ℓ)
    [CharP (ResidueField ↥A) ℓ]
    (fm : FibreModel N A ℓ (ResidueField ↥A) (IsLocalRing.residue ↥A))
    (cc : fm.CuspChart)
    (dataAll : ∀ (d : ℕ) [NeZero d], d ∣ N → ModularPolynomialData d)
    (hsep : (((dataAll N (dvd_refl N)).Φ.map
        (Polynomial.mapRingHom (Int.castRingHom (ResidueField ↥A)))).map
      (algebraMap (Polynomial (ResidueField ↥A)) (RatFunc (ResidueField ↥A)))).Separable)
    (hpres : fm.SpDivPreservesPrincipal Ideal.Quotient.mk_surjective dataAll hsep)
    (hsq : Squarefree N) (hsym : EvalSymm (dataAll N (dvd_refl N)).Φ)
    (data : ModularPolynomialData ℓ) (hKr : KroneckerCongruence ℓ data)
    (hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N ℓ)
    (hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N ℓ) :
    ∃ S : PlaceSpecialization A ℓ N data hKr (ResidueField ↥A) (IsLocalRing.residue ↥A) hα hβ,
      S.sp = fm.spPlace Ideal.Quotient.mk_surjective dataAll hsep ∧
      S.spPic0 = fm.spPic0 Ideal.Quotient.mk_surjective dataAll hsep := by sorry
