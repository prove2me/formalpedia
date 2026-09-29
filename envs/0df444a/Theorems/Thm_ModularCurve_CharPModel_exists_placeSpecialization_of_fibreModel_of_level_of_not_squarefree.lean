-- Prove2me | Theorems.Thm_ModularCurve_CharPModel_exists_placeSpecialization_of_fibreModel_of_level_of_not_squarefree
-- name    : ModularCurve.CharPModel.exists_placeSpecialization_of_fibreModel_of_level_of_not_squarefree
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:12.70306+00:00
-- url     : https://prove2.me/theorems/94a41b12-2dd0-532b-8096-295f7a4e4eb2
-- title:
--   Place specialisation at non-squarefree level prime to ℓ
-- statement:
--   Let $N$ be a nonzero natural number which is not squarefree, let $\ell$ be a prime not dividing $N$, and let $A$ be a valuation subring of $\overline{\mathbb{Q}}$ lying over $\ell$ in the sense that $\ell$, viewed in $\overline{\mathbb{Q}}$, is a non-unit of $A$. Let `data` be a modular polynomial datum of level $\ell$, i.e. a monic $\Phi \in \mathbb{Z}[X][Y]$ of degree $\psi(\ell)$ with $\Phi(j, j_\ell) = 0$, and assume the Kronecker congruence `hKr`: the reduction of $\Phi$ modulo $\ell$ equals $(C(X)^{\ell} - X)(C(X) - X^{\ell})$. Assume further that the two Hecke pull-back homomorphisms $\overline{\alpha}$ and $\overline{\beta}$ at level $N$ and prime $\ell$ over $\overline{\mathbb{Q}}$ are integral, that the residue field of $A$ has characteristic $\ell$ and is algebraically closed, and that a fibre model of level $N$ over $A$ with values in that residue field, along its canonical residue map, is given: a pair of subrings $B_{\mathrm{fin}}, B_{\mathrm{inf}}$ of the base change to $\overline{\mathbb{Q}}$ of the full modular function field of level $N$, containing the constants from $A$ and $\bar j, \bar j_N$ respectively $\bar j^{-1}$, integral over the corresponding affine bases, together with ring homomorphisms to the characteristic-$\ell$ modular function field of level $N$ compatible with constants and with $\bar j$, $\bar j_N$, $\bar j^{-1}$. Then the type `PlaceSpecialization` for $A$, $\ell$, $N$, `data`, `hKr`, the residue field of $A$ with its canonical residue map, and the two integrality hypotheses is nonempty: there exists a specialisation of places of the level-$N$ modular function field over $\overline{\mathbb{Q}}$ to places of its characteristic-$\ell$ counterpart, together with a homomorphism on degree-zero divisor classes, satisfying the order compatibilities recorded in that structure.
--
--   This is the non-squarefree branch of the level-uniform existence statement for place specialisations at a prime $\ell$ of good reduction, and is cited by [`ModularCurve.CharPModel.exists_placeSpecialization_of_fibreModel_of_level`](thm.html#ModularCurve.CharPModel.exists_placeSpecialization_of_fibreModel_of_level); the place specialisation is the device by which places and degree-zero divisor classes of the modular curve of level $N$ over $\overline{\mathbb{Q}}$ are reduced to characteristic $\ell$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_CharPModel_exists_placeSpecialization_of_fibreModel_of_level_of_not_squarefree.lean

import Definitions.Def_ModularCurve_PlaceSpecialization
import Definitions.Def_ModularCurve_FibreModel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open ModularCurve ModularCurve.CharPModel ValuationSubring AlgebraicCurve IsLocalRing
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000

theorem ModularCurve.CharPModel.exists_placeSpecialization_of_fibreModel_of_level_of_not_squarefree
    (N : ℕ) [NeZero N]
    (hnsq : ¬ Squarefree N)
    (ℓ : ℕ) [hℓ : Fact ℓ.Prime] (hℓN : ¬ ℓ ∣ N)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime ℓ)
    (data : ModularPolynomialData ℓ) (hKr : KroneckerCongruence ℓ data)
    (hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N ℓ)
    (hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N ℓ)
    [CharP (ResidueField ↥A) ℓ] [IsAlgClosed (ResidueField ↥A)]
    (fm : FibreModel N A ℓ (ResidueField ↥A) (IsLocalRing.residue ↥A)) :
    Nonempty (PlaceSpecialization A ℓ N data hKr (ResidueField ↥A)
        (IsLocalRing.residue ↥A) hα hβ) := by sorry
