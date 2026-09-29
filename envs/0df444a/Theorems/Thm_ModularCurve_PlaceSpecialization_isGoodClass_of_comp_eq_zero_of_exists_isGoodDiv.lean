-- Prove2me | Theorems.Thm_ModularCurve_PlaceSpecialization_isGoodClass_of_comp_eq_zero_of_exists_isGoodDiv
-- name    : ModularCurve.PlaceSpecialization.isGoodClass_of_comp_eq_zero_of_exists_isGoodDiv
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:46.056571+00:00
-- url     : https://prove2.me/theorems/c911749b-ba84-50ab-b10f-369bdbbcf5c3
-- title:
--   Vanishing of the component map implies a good class
-- statement:
--   Let $q$ be a prime, $A$ a valuation subring of $\overline{\mathbb{Q}}$, $N\ge 1$, $k$ an algebraically closed field of characteristic $q$, $\mathrm{red}:A\to k$ a ring homomorphism, `data` modular polynomial data at level $q$ satisfying the Kronecker congruence (its bivariate reduction modulo $q$ equals $(Y^{q}-X)(Y-X^{q})$), and assume the two level-raising embeddings $\bar\alpha,\bar\beta$ of $\overline{\mathbb{Q}}$-modular function fields from level $N$ to level $Nq$ are integral; let $P$ be a `PlaceSpecialization` for these data. Let $W$ be a nonempty finite set of places of $\mathrm{modularFunctionFieldC}\,k\,N$, each fixed by the square of the semilinear arithmetic Frobenius `arithFrobC q k N`, let $S$ be the finite set of pairs obtained from $W$ through `smulNodePairEmb (arithFrobC q k N)`, and let $e:\,$places$\,\to\mathbb{N}$ be positive on $W$, with widths $\varepsilon(s)=e(s_{1})$ on $S$ and $m=\sum_{s\in S}\operatorname{lcm}(\varepsilon)/\varepsilon(s)$. Let `comp` be an additive map from the subgroup of $\mathrm{Pic}^{0}$ of the level-$Nq$ curve over $\overline{\mathbb{Q}}$ fixed by the inertia subgroup of $A$ over $\mathbb{Q}$ to the component group attached to $\varepsilon$ (the dual of the kernel of the coordinate sum on $\mathbb{Z}^{S}$, modulo the image of the Gram map), subject to: for every degree-zero divisor $D$ whose support consists of places strictly of first or second type for $P$ and whose class lies in the inertia invariants, and every $s_{0}\in S$, $\mathrm{comp}[D]$ equals $\deg(P.\mathrm{sndDiv}\,D)$ times the class of the functional $\gamma\mapsto \varepsilon(s_{0})\gamma(s_{0})$. Assume further a principal divisor $G$ with support of the same strict type, $\deg(P.\mathrm{fstDiv}\,G)=m$ and $\deg(P.\mathrm{sndDiv}\,G)=-m$. Then any inertia-invariant class $x$ that is represented by some degree-zero divisor of strict support and satisfies $\mathrm{comp}(x)=0$ is a good class for $S$: there is a degree-zero divisor $D$ of strict support with class $x$ whose glue datum — the pushforward of $P.\mathrm{fstDiv}\,D$ along $P.\mathrm{reduceFst}$, the pushforward of $P.\mathrm{sndDiv}\,D$ along $P.\mathrm{reduceSnd}$, and the trivial unit component — is admissible, i.e. both divisors have degree zero and for each $s\in S$ the first vanishes at $s_{1}$ and the second at $s_{2}$.
--
--   This is the combinatorial criterion by which a class in the inertia invariants of the Jacobian at level $Nq$ is shown to be representable by a divisor glueing to an admissible datum on the reduction, the component group of the widths playing the role of the group of connected components of the Néron model at $q$. It is used in the construction of the Deligne–Rapoport model package and in the comparison of the resulting component maps with the Hecke action.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_PlaceSpecialization_isGoodClass_of_comp_eq_zero_of_exists_isGoodDiv.lean

import Definitions.Def_ModularCurve_GlueData
import Definitions.Def_ModularCurve_SupersingularNodePlaces
import Definitions.Def_ModularCurve_CoeffSemilinearAut

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
set_option Elab.async false
open AlgebraicCurve ModularCurve

theorem ModularCurve.PlaceSpecialization.isGoodClass_of_comp_eq_zero_of_exists_isGoodDiv (q : ℕ) [Fact q.Prime]
    (A : ValuationSubring (AlgebraicClosure ℚ)) (N : ℕ) [NeZero N] (k : Type*) [Field k]
    [CharP k q] (red : A →+* k) (data : ModularPolynomialData q)
    (hKr : KroneckerCongruence q data) (hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q)
    (hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q) [IsAlgClosed k]
    (P : PlaceSpecialization A q N data hKr k red hα hβ)
    (W : Finset (Place k (modularFunctionFieldC k N)))
    (hfix : ∀ w ∈ W, arithFrobC q k N • (arithFrobC q k N • w) = w)
    (hW0 : W.Nonempty)
    (e : Place k (modularFunctionFieldC k N) → ℕ) (hpos : ∀ w ∈ W, 0 < e w)
    (comp : ↥(inertiaInvariants A (N * q)) →+
      componentGroup (widthOfPlaces (arithFrobC q k N) W e))
    (hlaw : ∀ (D : ↥(Divisor.degZero (K := AlgebraicClosure ℚ)
          (F := ↥(modularFunctionFieldBar (N * q)))))
        (hH : Pic0.mk D ∈ inertiaInvariants A (N * q)),
        P.IsGoodDiv (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))) →
        ∀ s₀ : ↥(nodePairsOfPlaces (arithFrobC q k N) W),
          comp ⟨Pic0.mk D, hH⟩ =
            (P.sndDiv (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)))).degree •
              componentGroupProj (widthOfPlaces (arithFrobC q k N) W e)
                ((widthOfPlaces (arithFrobC q k N) W e s₀ : ℤ) •
                  (LinearMap.proj s₀ : (↥(nodePairsOfPlaces (arithFrobC q k N) W) → ℤ) →ₗ[ℤ] ℤ).comp
                    (characterLattice ↥(nodePairsOfPlaces (arithFrobC q k N) W)).subtype))
    (hG : ∃ G : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)),
        Divisor.IsPrincipal G ∧ P.IsGoodDiv G ∧
          (P.fstDiv G).degree = ((∑ s : ↥(nodePairsOfPlaces (arithFrobC q k N) W),
            Finset.univ.lcm (widthOfPlaces (arithFrobC q k N) W e) / widthOfPlaces (arithFrobC q k N) W e s : ℕ) : ℤ) ∧
          (P.sndDiv G).degree = -((∑ s : ↥(nodePairsOfPlaces (arithFrobC q k N) W),
            Finset.univ.lcm (widthOfPlaces (arithFrobC q k N) W e) / widthOfPlaces (arithFrobC q k N) W e s : ℕ) : ℤ))
    (x : ↥(inertiaInvariants A (N * q)))
    (hrep : ∃ D : ↥(Divisor.degZero (K := AlgebraicClosure ℚ)
            (F := ↥(modularFunctionFieldBar (N * q)))),
          P.IsGoodDiv (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))) ∧
            Pic0.mk D = (x : JZero (N * q)))
    (hx : comp x = 0) :
    P.IsGoodClass (nodePairsOfPlaces (arithFrobC q k N) W) (x : JZero (N * q)) := by sorry
