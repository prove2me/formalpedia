-- Prove2me | Theorems.Thm_ModularCurve_CharPModel_exists_placeSpecialization_of_fibreModel_of_level
-- name    : ModularCurve.CharPModel.exists_placeSpecialization_of_fibreModel_of_level
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:12.70306+00:00
-- url     : https://prove2.me/theorems/0c9d0ded-b2d4-5a43-8cf5-146d2de116bf
-- title:
--   Place specialisation from a fibre model at arbitrary level
-- statement:
--   Let $N$ be a nonzero natural number, let $\ell$ be a prime not dividing $N$, and let $A$ be a valuation subring of an algebraic closure $\overline{\mathbb{Q}}$ of $\mathbb{Q}$ lying over $\ell$ in the sense that $\ell$ is a non-unit of $A$. Let `data` consist of a monic polynomial $\Phi \in \mathbb{Z}[X][Y]$ of degree $\psi(\ell)$ annihilating the pair $(j, j_\ell)$ of $q$-expansions, and let `hKr` assert the Kronecker congruence, namely that the bivariate reduction of $\Phi$ modulo $\ell$ equals $(C(X)^{\ell} - X)\,(C(X) - X^{\ell})$. Let `hα` and `hβ` assert that the two Hecke homomorphisms $\overline{\alpha}$, $\overline{\beta}$ at level $N$ and index $\ell$ over $\overline{\mathbb{Q}}$ are integral ring maps. Assume the residue field of $A$ has characteristic $\ell$ and is algebraically closed, and let `fm` be a fibre model of level $N$ over $A$ with values in that residue field along the residue map: a pair of subrings $B_{\mathrm{fin}}, B_{\infty}$ of the base change to $\overline{\mathbb{Q}}$ of the full modular function field of level $N$ inside Laurent series, containing the constants from $A$, with $\bar j, \bar j_N \in B_{\mathrm{fin}}$ and $\bar j^{-1} \in B_{\infty}$, each element integral over the respective affine base subring, together with reduction homomorphisms to the level-$N$ modular function field over the residue field matching the constants, $\bar j$, $\bar j_N$ and $\bar j^{-1}$. Then the type `PlaceSpecialization` for these data is nonempty: there exists a specialisation structure consisting of a map from places of the level-$N$ modular function field over $\overline{\mathbb{Q}}$ to places over the residue field, an accompanying additive map $\mathrm{Pic}^0 \to \mathrm{Pic}^0$ of degree-zero divisor class groups, and the order-of-vanishing compatibilities for $j - a$, for poles of $j$, for $j_N - a$ and the further laws recorded in that structure.
--
--   This is the existence of a specialisation of places and of degree-zero divisor classes from the modular curve $X_0(N)$ over $\overline{\mathbb{Q}}$ to its fibre over a prime $\ell$ not dividing $N$, at the canonical residue pair attached to a valuation ring $A$ above $\ell$, with no squarefreeness restriction on $N$. It feeds the glued-specialisation statements for prolongation tuples and place widths used later in the level-lowering argument.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_CharPModel_exists_placeSpecialization_of_fibreModel_of_level.lean

import Definitions.Def_ModularCurve_PlaceSpecialization
import Definitions.Def_ModularCurve_FibreModel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open ModularCurve ModularCurve.CharPModel ValuationSubring AlgebraicCurve IsLocalRing
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000

theorem ModularCurve.CharPModel.exists_placeSpecialization_of_fibreModel_of_level
    (N : ℕ) [NeZero N]
    (ℓ : ℕ) [hℓ : Fact ℓ.Prime] (hℓN : ¬ ℓ ∣ N)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime ℓ)
    (data : ModularPolynomialData ℓ) (hKr : KroneckerCongruence ℓ data)
    (hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N ℓ)
    (hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N ℓ)
    [CharP (ResidueField ↥A) ℓ] [IsAlgClosed (ResidueField ↥A)]
    (fm : FibreModel N A ℓ (ResidueField ↥A) (IsLocalRing.residue ↥A)) :
    Nonempty (PlaceSpecialization A ℓ N data hKr (ResidueField ↥A)
        (IsLocalRing.residue ↥A) hα hβ) := by sorry
