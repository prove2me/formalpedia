-- Prove2me | Theorems.Thm_ModularCurve_PlaceSpecialization_exists_comp_sndDegLaw_coordMem_repOfKer_widthChar_of_isModel
-- name    : ModularCurve.PlaceSpecialization.exists_comp_sndDegLaw_coordMem_repOfKer_widthChar_of_isModel
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:46.056571+00:00
-- url     : https://prove2.me/theorems/cb6953b4-f899-560e-b221-8543777fc97c
-- title:
--   Component map of J₀(Nq) with second-copy degree law
-- statement:
--   Fix a prime $q$, a valuation subring $A$ of $\overline{\mathbb{Q}}$, a positive level $N$ with $q \nmid N$, and an algebraically closed field $k$ of characteristic $q$ together with a ring homomorphism $\mathrm{red} : A \to k$; let $\mathrm{data}$ be a modular polynomial datum for $q$ (a monic $\Phi \in \mathbb{Z}[X][Y]$ of degree $\psi(q)$ annihilating the pair $(j, j_q)$ of $q$-expansions) satisfying the Kronecker congruence $\Phi \bmod q = (Y^q - X)(Y - X^q)$, and let $h\alpha$, $h\beta$ assert integrality of the two degeneracy embeddings $\overline{F}(N) \to \overline{F}(Nq)$. Assume $\mathrm{red}$ is surjective, let $P$ be a place specialisation of level $N$ at $q$ for these data, let $W$ be a finite set of places of the geometric function field $\mathrm{modularFunctionFieldC}\,k\,N$ whose members are exactly the supersingular places, let $R$ be a prolongation tuple over $P$ which is a model (the two divisor laws and the two cusp laws), and which satisfies the regularity law and the node-value law for $W$ as well as the fixed-point order law, and let $e$ be a width function agreeing on $W$ with the characteristic-$q$ place width $\mathrm{placeWidthChar}\,q\,N$. Write $S$ for the finite set of node pairs $\{(w, \mathrm{arithFrobC}\,q\,k\,N \cdot w) : w \in W\}$, with widths given by $e$ of the first coordinate, and $\Phi(e)$ for the associated combinatorial component group, the quotient of $\mathrm{Hom}_{\mathbb{Z}}(\Lambda, \mathbb{Z})$ by the image of the Gram map of the width pairing, $\Lambda \subseteq \mathbb{Z}^S$ being the kernel of the sum-of-coordinates functional. Then there exists an additive homomorphism $\mathrm{comp}$ from the subgroup of inertia invariants of $J_0(Nq) = \mathrm{Pic}^0$ of $\mathrm{modularFunctionFieldBar}(Nq)$ over $\overline{\mathbb{Q}}$, the elements fixed by the inertia subgroup of $A$ over $\mathbb{Q}$, to $\Phi(e)$ such that: (i) for every degree-zero divisor $D$ whose class is inertia-invariant and all of whose support points are strict for the first or the second copy, and for every $s_0 \in S$, the value of $\mathrm{comp}$ on the class of $D$ equals the degree of the part of $D$ supported at second-copy-strict points times the class of $e(s_0)$ times the coordinate functional at $s_0$ restricted to $\Lambda$; (ii) for every $s \in S$ the class of the coordinate functional at $s$ restricted to $\Lambda$ lies in the range of $\mathrm{comp}$; (iii) every element of the kernel of $\mathrm{comp}$ is the class of a degree-zero divisor supported at first- or second-copy-strict points.
--
--   This is the combinatorial component-group map attached to the semistable reduction of $J_0(Nq)$ at $q$, in the form valid for all primes $q$ including $2$ and $3$, where the widths of the supersingular nodes are the characteristic-$q$ widths rather than the tame ones. It feeds the next step in the analysis of the component group of $J_0(Nq)$ at $q$, where the widths themselves are produced alongside the map.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_PlaceSpecialization_exists_comp_sndDegLaw_coordMem_repOfKer_widthChar_of_isModel.lean

import Definitions.Def_ModularCurve_GlueData
import Definitions.Def_ModularCurve_CoeffSemilinearAut
import Definitions.Def_ModularCurve_PlaceWidthChar
import Definitions.Def_ModularCurve_ProlongationTuple

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicCurve

theorem ModularCurve.PlaceSpecialization.exists_comp_sndDegLaw_coordMem_repOfKer_widthChar_of_isModel
    {q : ℕ} [Fact q.Prime]
    {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N] {k : Type*} [Field k]
    [CharP k q] {red : A →+* k} {data : ModularPolynomialData q}
    {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q} [IsAlgClosed k]
    [DecidableEq k] (hqN : ¬ q ∣ N)
    (hred : Function.Surjective red)
    (P : PlaceSpecialization A q N data hKr k red hα hβ)
    (W : Finset (Place k (modularFunctionFieldC k N)))
    (hW : ∀ w, w ∈ W ↔ w ∈ ssPlaces q N k)
    (R : ProlongationTuple P) (hR : R.IsModel) (hRL : R.RegularityLaw W) (hNV : R.NodeValueLaw W)
    (hO : R.OrderLawFixed)
    (e : Place k (modularFunctionFieldC k N) → ℕ)
    (he : ∀ w ∈ W, e w = placeWidthChar q N w) :
    ∃ (comp : ↥(inertiaInvariants A (N * q)) →+
        componentGroup (widthOfPlaces (arithFrobC q k N) W e)),
      (∀ (D : ↥(Divisor.degZero (K := AlgebraicClosure ℚ)
            (F := ↥(modularFunctionFieldBar (N * q)))))
          (hH : Pic0.mk D ∈ inertiaInvariants A (N * q)),
          P.IsGoodDiv (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))) →
          ∀ s₀ : ↥(nodePairsOfPlaces (arithFrobC q k N) W),
            comp ⟨Pic0.mk D, hH⟩ =
              (P.sndDiv (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)))).degree •
                componentGroupProj (widthOfPlaces (arithFrobC q k N) W e)
                  ((widthOfPlaces (arithFrobC q k N) W e s₀ : ℤ) •
                    (LinearMap.proj s₀ : (↥(nodePairsOfPlaces (arithFrobC q k N) W) → ℤ) →ₗ[ℤ] ℤ).comp
                      (characterLattice ↥(nodePairsOfPlaces (arithFrobC q k N) W)).subtype)) ∧
      (∀ s : ↥(nodePairsOfPlaces (arithFrobC q k N) W),
        componentGroupProj (widthOfPlaces (arithFrobC q k N) W e)
          ((LinearMap.proj s : (↥(nodePairsOfPlaces (arithFrobC q k N) W) → ℤ) →ₗ[ℤ] ℤ).comp
            (characterLattice ↥(nodePairsOfPlaces (arithFrobC q k N) W)).subtype) ∈ comp.range) ∧
      (∀ x : ↥(inertiaInvariants A (N * q)), comp x = 0 →
        ∃ D : ↥(Divisor.degZero (K := AlgebraicClosure ℚ)
            (F := ↥(modularFunctionFieldBar (N * q)))),
          P.IsGoodDiv (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))) ∧
            Pic0.mk D = (x : JZero (N * q))) := by sorry
