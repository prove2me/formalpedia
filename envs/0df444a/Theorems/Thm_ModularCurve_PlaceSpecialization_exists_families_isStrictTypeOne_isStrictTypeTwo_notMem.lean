-- Prove2me | Theorems.Thm_ModularCurve_PlaceSpecialization_exists_families_isStrictTypeOne_isStrictTypeTwo_notMem
-- name    : ModularCurve.PlaceSpecialization.exists_families_isStrictTypeOne_isStrictTypeTwo_notMem
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:46.056571+00:00
-- url     : https://prove2.me/theorems/40ba0fd8-3984-5c48-9507-9a8257775831
-- title:
--   Arbitrarily many strict type one and type two places avoiding B
-- statement:
--   Fix a prime $q$, a valuation subring $A$ of $\overline{\mathbb Q}$, an algebraically closed field $k$ of characteristic $q$, a ring homomorphism $\mathrm{red}\colon A \to k$, and modular polynomial data `data` for $q$ (a monic $\Phi \in \mathbb Z[X][Y]$ of degree $\psi(q)$ annihilating the pair $(j, j_q)$) satisfying the Kronecker congruence `hKr`, i.e. the reduction of $\Phi$ modulo $q$ equals $(X^q - Y)(X - Y^q)$ in the bivariate sense encoded by `KroneckerCongruence`; assume also that the two Hecke maps $\bar\alpha$, $\bar\beta$ at level $N = 1$ and prime $q$ have integral underlying ring homomorphisms (`hα`, `hβ`). Let $P$ be a place specialisation datum of type `PlaceSpecialization A q 1 data hKr k red hα hβ`, whose component `sp` sends places of $\overline{\mathbb Q}(\text{modularFunctionFieldBar }1)$ to places of the geometric level-one function field $\mathrm{modularFunctionFieldC}\,k\,1$; here a place of $F/K$ is a valuation subring of $F$ containing $K$, proper, and a principal ideal ring. For a place $W$ of $\mathrm{modularFunctionFieldBar}(1 \cdot q)$ over $\overline{\mathbb Q}$, write $\mathrm{redFst}\,W = P.\mathrm{sp}(W|_{\bar\alpha})$ and $\mathrm{redSnd}\,W = P.\mathrm{sp}(W|_{\bar\beta})$, the restrictions being along the two Hecke embeddings, and let $\varphi$ denote `frobOnPlacesGeomLevel k 1 data hKr`. Then for every finite set $B$ of places of $\mathrm{modularFunctionFieldC}\,k\,1$ over $k$ and all $m_1, m_2 \in \mathbb N$ there exist families $Q_1 \colon \mathrm{Fin}\,m_1$ and $Q_2 \colon \mathrm{Fin}\,m_2$ of places of $\mathrm{modularFunctionFieldBar}(1 \cdot q)$ over $\overline{\mathbb Q}$ such that each $Q_1(i)$ is of strict type one, $\varphi(\mathrm{redFst}\,Q_1(i)) = \mathrm{redSnd}\,Q_1(i)$ and $\varphi^2(\mathrm{redFst}\,Q_1(i)) \neq \mathrm{redFst}\,Q_1(i)$; each $Q_2(j)$ is of strict type two, $\mathrm{redFst}\,Q_2(j) = \varphi(\mathrm{redSnd}\,Q_2(j))$ and $\varphi^2(\mathrm{redSnd}\,Q_2(j)) \neq \mathrm{redSnd}\,Q_2(j)$; the maps $i \mapsto \mathrm{redFst}\,Q_1(i)$ and $j \mapsto \mathrm{redSnd}\,Q_2(j)$ are injective; and all these reductions lie outside $B$.
--
--   This is the general-position supply of base points on the two components of the reduction of $X_0(q)$ at $q$: arbitrarily many places of each of the two strict Frobenius types, with pairwise distinct reductions on the level-one $j$-line and with those reductions avoiding any prescribed finite set. It is used in the construction of level-one prolongation pairs, namely by [`ModularCurve.PlaceSpecialization.LevelOneProlongationPair.exists_commonUnit_ord_eq_one_of_mem_levelOne`](thm.html#ModularCurve.PlaceSpecialization.LevelOneProlongationPair.exists_commonUnit_ord_eq_one_of_mem_levelOne) and [`ModularCurve.PlaceSpecialization.LevelOneProlongationPair.exists_ord_eq_one_forall_redFst_redSnd_notMem`](thm.html#ModularCurve.PlaceSpecialization.LevelOneProlongationPair.exists_ord_eq_one_forall_redFst_redSnd_notMem), where functions with prescribed simple zeros away from a bad set are needed.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_PlaceSpecialization_exists_families_isStrictTypeOne_isStrictTypeTwo_notMem.lean

import Mathlib
import Definitions.Def_ModularCurve_LevelOneGlueData

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option synthInstance.maxHeartbeats 400000
set_option autoImplicit false
open AlgebraicCurve ModularCurve

theorem ModularCurve.PlaceSpecialization.exists_families_isStrictTypeOne_isStrictTypeTwo_notMem
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    {k : Type*} [Field k] [CharP k q] [IsAlgClosed k] [DecidableEq k] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) 1 q} {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) 1 q}
    (P : PlaceSpecialization A q 1 data hKr k red hα hβ)
    (B : Finset (Place k ↥(modularFunctionFieldC k 1))) (m₁ m₂ : ℕ) :
    ∃ (Q₁ : Fin m₁ → Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)))
      (Q₂ : Fin m₂ → Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q))),
      (∀ i, P.IsStrictTypeOne (Q₁ i)) ∧ (∀ j, P.IsStrictTypeTwo (Q₂ j)) ∧
      (Function.Injective fun i => P.redFst (Q₁ i)) ∧
      (Function.Injective fun j => P.redSnd (Q₂ j)) ∧
      (∀ i, P.redFst (Q₁ i) ∉ B) ∧ (∀ j, P.redSnd (Q₂ j) ∉ B) := by sorry
