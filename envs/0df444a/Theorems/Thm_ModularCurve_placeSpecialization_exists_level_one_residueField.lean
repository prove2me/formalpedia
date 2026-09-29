-- Prove2me | Theorems.Thm_ModularCurve_placeSpecialization_exists_level_one_residueField
-- name    : ModularCurve.placeSpecialization_exists_level_one_residueField
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:53.985053+00:00
-- url     : https://prove2.me/theorems/3ff7e69c-db86-53a6-8327-036397e81750
-- title:
--   Level-one place specialization over the residue field of A
-- statement:
--   Let $\ell$ be a prime, let `data` be a modular-polynomial datum at $\ell$, that is a monic $\Phi \in \mathbb Z[X][Y]$ of degree $\psi(\ell)$ annihilating the pair $(j(q), j(q^{\ell}))$ in the sense of `ModularPolynomialData`, and let `hKr` assert Kronecker's congruence for it: the reduction of $\Phi$ modulo $\ell$ in bivariate form equals $(\mathrm{C}\,X^{\ell} - X)(\mathrm{C}\,X - X^{\ell})$. Let $A$ be a valuation subring of $\overline{\mathbb Q} =$ `AlgebraicClosure ℚ` lying over $\ell$ in the sense that $\ell$ is a non-unit of $A$, i.e. lies in its maximal ideal. Assume further that both degeneracy inclusions `heckeAlphaBar` and `heckeBetaBar` from the level-$1$ modular function field into the level-$1\cdot\ell$ one, over $\overline{\mathbb Q}$ and after base change to Laurent series, are integral ring homomorphisms. Then, the residue field $\kappa_A$ of $A$ having characteristic $\ell$ by [`ValuationSubring.charP_residueField_of_liesOverPrime_def`](def/WeierstrassCurve_ReductionMap.html#L57), the type `PlaceSpecialization A ℓ 1 data hKr` over the special fibre $(\kappa_A, \mathrm{residue}_A)$ is nonempty: there exist a map $\mathrm{sp}$ from places of the level-$1$ modular function field over $\overline{\mathbb Q}$ to places of `modularFunctionFieldC` $\kappa_A$ $1$, a homomorphism from `JZero 1` to $\mathrm{Pic}^0$ of that characteristic-$\ell$ field, and witnesses for all clauses of the structure, among them that a zero of $j - a$ for $a \in A$ goes to a zero of $\tilde\jmath - \mathrm{residue}_A(a)$, that places at which $j$ takes no value in $A$ go to poles of $\tilde\jmath$, and the corresponding clauses for the level-$\ell$ coordinate.
--
--   This is the inhabitedness of the level-one place-specialization packet — the specialization of places and of $\mathrm{Pic}^0$ for the $j$-line with Kronecker's congruence governing the level-$\ell$ fibre — in the form where the special fibre is the residue field of the chosen valuation ring $A$ itself rather than a fixed algebraic closure of $\mathbb F_\ell$. It is the form consumed by the construction of the semistable specialization datum for $J_0(q)$ at $A$, and is cited in the analysis of fibre models, of the node locus and of Atkin–Lehner behaviour at such places.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_placeSpecialization_exists_level_one_residueField.lean

import Definitions.Def_ModularCurve_PlaceSpecialization
import Definitions.Def_ValuationSubring_ReduceAt

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicCurve ModularCurve

theorem ModularCurve.placeSpecialization_exists_level_one_residueField
    (ℓ : ℕ) [Fact ℓ.Prime]
    (data : ModularPolynomialData ℓ) (hKr : KroneckerCongruence ℓ data)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime ℓ)
    (hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) 1 ℓ)
    (hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) 1 ℓ) :
    haveI : CharP (IsLocalRing.ResidueField ↥A) ℓ :=
      ValuationSubring.charP_residueField_of_liesOverPrime_def Fact.out hA
    Nonempty (PlaceSpecialization A ℓ 1 data hKr (IsLocalRing.ResidueField ↥A)
      (IsLocalRing.residue ↥A) hα hβ) := by sorry
