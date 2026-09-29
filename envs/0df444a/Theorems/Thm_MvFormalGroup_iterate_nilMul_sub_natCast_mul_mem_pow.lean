-- Prove2me | Theorems.Thm_MvFormalGroup_iterate_nilMul_sub_natCast_mul_mem_pow
-- name    : MvFormalGroup.iterate_nilMul_sub_natCast_mul_mem_pow
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:55.856965+00:00
-- url     : https://prove2.me/theorems/0f053a8b-4a53-5440-b604-1f467d1e3547
-- title:
--   Multiples of a J^k-point of a formal group
-- statement:
--   Let $B$ be a commutative ring and let $F$ be a $g$-dimensional formal group law over $B$, that is, a family $F_i$ ($i \in \mathrm{Fin}\,g$) of formal power series in the variables indexed by $\mathrm{Fin}\,g \sqcup \mathrm{Fin}\,g$ with vanishing constant coefficients, with the coefficient of each linear monomial $X_{\mathrm{inl}\,j}$ and of each $X_{\mathrm{inr}\,j}$ in $F_i$ equal to $1$ if $i = j$ and $0$ otherwise, and satisfying the associativity identity between the two substitutions of $F$ into $F$. Let $B'$ be a commutative $B$-algebra, $J \subseteq B'$ an ideal, and $\nu$ a natural number with $J^{\nu+1} = 0$. Let $k \geq 1$, let $s : \mathrm{Fin}\,g \to B'$ satisfy $s_i \in J^k$ for all $i$, and let $m$ be a natural number and $i$ an index. Here the formal sum $F.\mathrm{nilMul}\,\nu\,t\,s$ of two tuples is formed componentwise by evaluating, at the concatenated tuple $(t,s)$, the polynomial truncation of $F_i$ keeping those monomials whose exponent in each variable is at most $\nu$. The assertion is that the $m$-fold iterate of $t \mapsto F.\mathrm{nilMul}\,\nu\,t\,s$ applied to the zero tuple has $i$-th component congruent to $m \cdot s_i$ modulo $J^{k+1}$.
--
--   This is the formal-group half of Katz's lemma on multiplication by $m$ on infinitesimal points: the $m$-fold formal sum of a $J^k$-point agrees with $m$ times it modulo $J^{k+1}$, so that multiplication by an integer killing $B'$ raises the level of a point by one. It is used in the proof of [`GoodReductionJacobian.RelativeGroupLaw.nsmul_pow_eq_one_of_isInfinitesimal`](thm.html#GoodReductionJacobian.RelativeGroupLaw.nsmul_pow_eq_one_of_isInfinitesimal), where iterating the statement shows that a suitable power of such an integer annihilates every infinitesimal point.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_MvFormalGroup_iterate_nilMul_sub_natCast_mul_mem_pow.lean

import Definitions.Def_AlgebraicGeometry_FormalGroupAlongSection

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MvFormalGroup

theorem MvFormalGroup.iterate_nilMul_sub_natCast_mul_mem_pow
    {B : Type} [CommRing B] {g : ℕ} (F : MvFormalGroup g B)
    {B' : Type} [CommRing B'] [Algebra B B'] (J : Ideal B') (ν : ℕ) (hJ : J ^ (ν + 1) = ⊥)
    (k : ℕ) (hk : 1 ≤ k) (s : Fin g → B') (hs : ∀ i, s i ∈ J ^ k) (m : ℕ) (i : Fin g) :
    ((fun t : Fin g → B' => F.nilMul ν t s)^[m] 0) i - (m : B') * s i ∈ J ^ (k + 1) := by sorry
