-- Prove2me | Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_setOf_reduceFst_eq_and_forall_mem_iff_evalAt_eq_zero_finite
-- name    : ModularCurve.PlaceSpecialization.ProlongationTuple.setOf_reduceFst_eq_and_forall_mem_iff_evalAt_eq_zero_finite
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:45.66333+00:00
-- url     : https://prove2.me/theorems/e0661161-97a9-5bae-8209-da8429b9107a
-- title:
--   Finiteness of places with prescribed node-ring vanishing ideal
-- statement:
--   Fix a prime $q$, a valuation subring $A$ of $\overline{\mathbb Q}$, a nonzero natural number $N$, a field $k$ of characteristic $q$ and a ring homomorphism $red : A \to k$; fix further modular polynomial data `data` for $q$ (a monic $\Phi \in \mathbb Z[X][Y]$ of degree $\psi(q)$ annihilating the pair $(j, j_q)$) together with a proof `hKr` that its bivariate reduction mod $q$ equals $(X^q - Y)(X - Y^q)$ in the appropriate Kronecker form, proofs `hα`, `hβ` that the two Hecke correspondence embeddings $\mathrm{heckeAlphaBar}$, $\mathrm{heckeBetaBar}$ of level $N$ and degree $q$ over $\overline{\mathbb Q}$ are integral ring maps, and a place specialisation datum $P$ for these choices. Let $R$ be a prolongation tuple over $P$, let $K$ be an intermediate field of $\overline{\mathbb Q}/\mathbb Q$, let $w$ be a place of the level-$N$ modular function field $\mathrm{modularFunctionFieldC}\ k\ N$ over $k$, and let $\mathfrak q \neq 0$ be an ideal of the subring $R.\mathrm{nodeIntegersOver}\ K\ w$ of $\mathrm{modularFunctionFieldBar}(Nq)$, consisting of those elements lying in $R.\mathrm{nodeIntegers}\ w$ whose Laurent series lies in $\mathrm{NodeLocalized.fieldOver}\ (Nq)\ K$. Then the set of places $V$ of $\mathrm{modularFunctionFieldBar}(Nq)$ over $\overline{\mathbb Q}$ (valuation subrings containing the base field, proper, with principal ideals) satisfying both $P.\mathrm{reduceFst}\,V = w$, that is $P.\mathrm{sp}$ applied to the restriction of $V$ along $\mathrm{heckeAlphaBar}$ equals $w$, and $g' \in \mathfrak q \iff V.\mathrm{evalAt}\,g' = 0$ for every $g'$ in $R.\mathrm{nodeIntegersOver}\ K\ w$, is finite.
--
--   This is the finiteness of the fibre of places above a node with prescribed vanishing ideal on the node ring, an instance of the classical fact that a nonzero element of a function field has only finitely many zeros. It supports the node-counting arguments attached to the $uv$-crossing model, being cited by [`ModularCurve.PlaceSpecialization.ProlongationTuple.exists_reduceFst_eq_and_evalAt_y_eq_of_ringEquiv_uvCrossingModel`](thm.html#ModularCurve.PlaceSpecialization.ProlongationTuple.exists_reduceFst_eq_and_evalAt_y_eq_of_ringEquiv_uvCrossingModel) and by [`ModularCurve.PlaceSpecialization.ProlongationTuple.ord_y_sub_algebraMap_evalAt_eq_one_of_ringEquiv_uvCrossingModel`](thm.html#ModularCurve.PlaceSpecialization.ProlongationTuple.ord_y_sub_algebraMap_evalAt_eq_one_of_ringEquiv_uvCrossingModel).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_setOf_reduceFst_eq_and_forall_mem_iff_evalAt_eq_zero_finite.lean

import Mathlib
import Definitions.Def_ModularCurve_NodeDepth

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve ModularCurve ModularCurve.PlaceSpecialization

theorem ModularCurve.PlaceSpecialization.ProlongationTuple.setOf_reduceFst_eq_and_forall_mem_iff_evalAt_eq_zero_finite
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
    {k : Type*} [Field k] [CharP k q] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q} {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
    {P : PlaceSpecialization A q N data hKr k red hα hβ}
    (R : ProlongationTuple P) (K : IntermediateField ℚ (AlgebraicClosure ℚ))
    (w : Place k (modularFunctionFieldC k N))
    (𝔮 : Ideal ↥(R.nodeIntegersOver K w)) (h𝔮0 : 𝔮 ≠ ⊥) :
    Set.Finite {V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) | (P.reduceFst V = w ∧
      ∀ g' : ↥(R.nodeIntegersOver K w), g' ∈ 𝔮 ↔ V.evalAt ((g' : ↥(modularFunctionFieldBar (N * q)))) = 0)} := by sorry
