-- Prove2me | Theorems.Thm_ModularCurve_PlaceSpecialization_red_surjective
-- name    : ModularCurve.PlaceSpecialization.red_surjective
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:46.056571+00:00
-- url     : https://prove2.me/theorems/3869219e-b15d-5bb5-94c1-267ab4bdd545
-- title:
--   Place specialization at level one forces red surjective
-- statement:
--   Let $q$ be a prime, let $A$ be a valuation subring of $\overline{\mathbb Q}$ (an algebraic closure of $\mathbb Q$), let $k$ be a field of characteristic $q$ and let $\mathrm{red} \colon A \to k$ be a ring homomorphism. Let `data` consist of a monic $\Phi \in \mathbb Z[X][Y]$ of degree $\psi(q)$ annihilating the pair $(j, j(q\,\cdot))$ of $q$-expansions, and let `hKr` be the Kronecker congruence for it, namely that reducing both sets of coefficients modulo $q$ turns $\Phi$ into $(C(X)^q - X)(C(X) - X^q)$. Let `hα`, `hβ` assert that the two degeneracy embeddings `heckeAlphaBar` and `heckeBetaBar` of the base-changed modular function field of level $1$ into that of level $1 \cdot q$, over $\overline{\mathbb Q}$, are integral ring homomorphisms. Finally let $P$ be a term of the structure `PlaceSpecialization` for these data at level $N = 1$: it provides a map `sp` from places of $\overline{\mathbb Q}(j)$-type function field `modularFunctionFieldBar 1` to places of `modularFunctionFieldC k 1` over $k$, a homomorphism from `JZero 1` to `Pic0 k (modularFunctionFieldC k 1)`, clauses relating the valuations of $j - a$ and of $j$ at $w$ to those of the mod-$q$ coordinate $\tilde\jmath - \mathrm{red}\,a$ and $\tilde\jmath$ at `sp w` (for $a \in A$), similar clauses for the level coordinate, and further compatibility clauses, among them the surjectivity of `sp`. The conclusion is that $\mathrm{red}$ is surjective: every element of $k$ is $\mathrm{red}\,a$ for some $a \in A$.
--
--   This is a genericity constraint on the target of a level-one place specialization packet: the existence of such a packet over $k$ forces $k$ to be exhausted by the reductions of elements of $A$. It is used in the level-one prolongation-pair development, for instance in the one-sided divisor law and in the production of units and of elements with prescribed nonvanishing reduction.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_PlaceSpecialization_red_surjective.lean

import Mathlib
import Definitions.Def_ModularCurve_PlaceSpecialization

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

open AlgebraicCurve ModularCurve

theorem ModularCurve.PlaceSpecialization.red_surjective
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    {k : Type*} [Field k] [CharP k q] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) 1 q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) 1 q}
    (P : PlaceSpecialization A q 1 data hKr k red hα hβ) : Function.Surjective red := by sorry
