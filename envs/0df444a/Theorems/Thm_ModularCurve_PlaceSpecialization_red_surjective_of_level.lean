-- Prove2me | Theorems.Thm_ModularCurve_PlaceSpecialization_red_surjective_of_level
-- name    : ModularCurve.PlaceSpecialization.red_surjective_of_level
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:46.056571+00:00
-- url     : https://prove2.me/theorems/52a9b7a0-07e3-5fa1-a292-78bc3856b939
-- title:
--   Surjectivity of the reduction map of a level-N place specialisation
-- statement:
--   Let $q$ be a prime, let $A$ be a valuation subring of $\overline{\mathbb Q}$ (an algebraic closure of $\mathbb Q$), let $N$ be a nonzero natural number, let $k$ be a field of characteristic $q$, and let $\mathrm{red} \colon A \to k$ be a ring homomorphism. Let `data` be a `ModularPolynomialData` for $q$, that is a monic $\Phi \in \mathbb Z[X][Y]$ of degree $\psi(q)$ in $Y$ annihilating the pair consisting of the $q$-expansion substitution and $j(q^N)$-datum used in the project's modular equation, and let `hKr` assert the Kronecker congruence for it: the coefficientwise reduction of $\Phi$ modulo $q$ equals $(C(X)^q - X)(C(X) - X^q)$ in $(\mathbb Z/q)[X][Y]$. Let `hα` and `hβ` assert that the two degeneracy embeddings `heckeAlphaBar` and `heckeBetaBar`, from the base change to $\overline{\mathbb Q}$ of the full level-$N$ modular function field inside Laurent series to the corresponding field of level $N q$, are integral ring homomorphisms. Finally, let $P$ be a `PlaceSpecialization` for these data: a structure packaging a map `sp` from places of the level-$N$ modular function field over $\overline{\mathbb Q}$ to places of `modularFunctionFieldC k N` $= k(j, j_N)$ over $k$, a homomorphism `spPic0` from $\mathrm{Pic}^0$ of the level-$N$ curve over $\overline{\mathbb Q}$ to $\mathrm{Pic}^0$ of the curve over $k$, and compatibility conditions, among them that positivity of the order of $j - a$ at a place $w$ (for $a \in A$) implies positivity of the order of $j - \mathrm{red}(a)$ at `sp w`, that if no $a \in A$ gives $j - a$ positive order at $w$ then $j$ has a pole at `sp w`, the analogous conditions for $j_N$, and surjectivity of `sp`. The conclusion is that $\mathrm{red}$ is surjective: every element of $k$ is $\mathrm{red}(a)$ for some $a \in A$.
--
--   The statement says that a specialisation of the level-$N$ modular curve forces the residue map $A \to k$ to be onto, so that $k$ is exhausted by reductions of elements of the valuation ring; the level-one case is the special case $N = 1$. It is used by the prolongation-tuple lemmas about component charts and models attached to a place specialisation.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_PlaceSpecialization_red_surjective_of_level.lean

import Mathlib
import Definitions.Def_ModularCurve_PlaceSpecialization

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

open AlgebraicCurve ModularCurve

theorem ModularCurve.PlaceSpecialization.red_surjective_of_level
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
    {k : Type*} [Field k] [CharP k q] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
    (P : PlaceSpecialization A q N data hKr k red hα hβ) : Function.Surjective red := by sorry
