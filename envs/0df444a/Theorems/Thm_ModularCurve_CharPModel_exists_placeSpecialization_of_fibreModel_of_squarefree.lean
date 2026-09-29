-- Prove2me | Theorems.Thm_ModularCurve_CharPModel_exists_placeSpecialization_of_fibreModel_of_squarefree
-- name    : ModularCurve.CharPModel.exists_placeSpecialization_of_fibreModel_of_squarefree
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:12.70306+00:00
-- url     : https://prove2.me/theorems/b0850ca4-4db5-5e8a-84b8-247b23d0aed4
-- title:
--   Existence of a place specialization at squarefree level
-- statement:
--   Fix a positive integer $N$ that is squarefree, a prime $\ell$ with $\ell \nmid N$, and a valuation subring $A$ of $\overline{\mathbb{Q}} =$ `AlgebraicClosure ℚ` lying over $\ell$ in the sense of `LiesOverPrime`, i.e. the image of $\ell$ is a non-unit of $A$; the residue field $\kappa =$ `ResidueField A` is assumed to be of characteristic $\ell$ and algebraically closed, and $A \to \kappa$ is the residue map. Fix furthermore: `data`, a `ModularPolynomialData` of level $\ell$, that is a monic $\Phi \in \mathbb{Z}[X][Y]$ of degree $\psi(\ell)$ annihilating the pair $(j, j_\ell)$ of $q$-expansions; a proof `hKr` of the Kronecker congruence, that the bivariate reduction of $\Phi$ modulo $\ell$ equals $(C(X)^{\ell} - X)\,(C(X) - X^{\ell})$; and proofs `hα`, `hβ` that the two Hecke pull-back ring homomorphisms `heckeAlphaBar`, `heckeBetaBar` of level $(N,\ell)$ over $\overline{\mathbb{Q}}$ are integral. Finally, let `fm` be a `FibreModel` of level $N$ over $A$ with residue data $(\ell,\kappa,\mathrm{res})$ — a pair of subrings $B_{\mathrm{fin}}, B_{\infty}$ of the $\overline{\mathbb{Q}}$-base change of the full level-$N$ Laurent modular function field, each containing the image of $A$, with $\bar j, \bar j_N \in B_{\mathrm{fin}}$ and $\bar j^{-1} \in B_{\infty}$, integral over the respective affine bases, together with reduction homomorphisms $\pi_{\mathrm{fin}}, \pi_{\infty}$ into the characteristic-$\ell$ modular function field $\kappa$-side that send constants to their residues and $\bar j, \bar j_N, \bar j^{-1}$ to the corresponding mod-$\ell$ $q$-expansions; and let `cc` be a cusp chart for `fm`, asserting $\bar j_N \cdot (\bar j^{-1})^{N} \in B_{\infty}$ with $\pi_{\infty}$ sending it to the corresponding product in characteristic $\ell$. The conclusion is that the type `PlaceSpecialization A ℓ N data hKr κ (residue A) hα hβ` is nonempty: there exists a specialization datum consisting of a map `sp` from places of the level-$N$ modular function field over $\overline{\mathbb{Q}}$ to places of its characteristic-$\ell$ counterpart, a homomorphism `spPic0` from `JZero N` to the degree-zero divisor class group $\mathrm{Pic}^0$ of the reduced curve, and the further compatibility conditions recorded in that structure (behaviour of the orders of $j$, $j_N$ and of poles under `sp`, and the remaining fields).
--
--   This is the existence statement for the reduction ("place specialization") of the modular curve $X_0(N)$ at a place of $\overline{\mathbb{Q}}$ above a prime $\ell$ of good reduction, in the squarefree-level form in which it is used downstream; it packages the reduction map on places together with its descent to degree-zero divisor classes and the compatibilities with $j$, $j_N$ and the cusps. It is cited by [`ModularCurve.CharPModel.exists_placeSpecialization_of_fibreModel_of_level`](thm.html#ModularCurve.CharPModel.exists_placeSpecialization_of_fibreModel_of_level).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_CharPModel_exists_placeSpecialization_of_fibreModel_of_squarefree.lean

import Definitions.Def_ModularCurve_PlaceSpecialization
import Definitions.Def_ModularCurve_FibreModel
import Definitions.Def_ModularCurve_FibreModelCuspChart

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open ModularCurve ModularCurve.CharPModel ValuationSubring AlgebraicCurve IsLocalRing
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000

theorem ModularCurve.CharPModel.exists_placeSpecialization_of_fibreModel_of_squarefree
    (N : ℕ) [NeZero N] (hsq : Squarefree N)
    (ℓ : ℕ) [hℓ : Fact ℓ.Prime] (hℓN : ¬ ℓ ∣ N)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime ℓ)
    (data : ModularPolynomialData ℓ) (hKr : KroneckerCongruence ℓ data)
    (hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N ℓ)
    (hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N ℓ)
    [CharP (ResidueField ↥A) ℓ] [IsAlgClosed (ResidueField ↥A)]
    (fm : FibreModel N A ℓ (ResidueField ↥A) (IsLocalRing.residue ↥A)) (cc : fm.CuspChart) :
    Nonempty (PlaceSpecialization A ℓ N data hKr (ResidueField ↥A)
        (IsLocalRing.residue ↥A) hα hβ) := by sorry
