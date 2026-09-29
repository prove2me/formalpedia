-- Prove2me | Theorems.Thm_IharaTower_RungAssembly_deltaComb_two
-- name    : IharaTower.RungAssembly.deltaComb_two
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:57.239308+00:00
-- url     : https://prove2.me/theorems/fa52ea00-cff3-5a7b-9fbe-f303e714bb35
-- title:
--   Rung element of a two-leg datum as a quadratic form
-- statement:
--   Let $\mathcal{O}$ be a commutative ring, let $T$ and $T'$ be commutative $\mathcal{O}$-algebras, let $M$ be an abelian group carrying compatible $T$- and $\mathcal{O}$-module structures (a scalar tower over $\mathcal{O}$), and likewise $M'$ over $T'$. Let $P$ be a level pairing for $(T,M)$, that is an $\mathcal{O}$-bilinear map $B\colon M \to M \to \mathcal{O}$ which is self-adjoint for the $T$-action ($B(t\cdot m,n)=B(m,t\cdot n)$) and whose associated map $M \to \operatorname{Hom}_{\mathcal{O}}(M,\mathcal{O})$ is bijective, and let $P'$ be such a pairing for $(T',M')$. Let $L$ be a leg datum with two legs relative to $P$ and $P'$: $\mathcal{O}$-linear maps $i_k\colon M \to M'$ and $j_k\colon M' \to M$ for $k \in \{0,1\}$ with $P.B(j_k m', m) = P'.B(m', i_k m)$, together with a table $(t_{kk'})$ of elements of $T$ such that $j_k \circ i_{k'}$ is multiplication by $t_{kk'}$ on $M$. Let $t_{00},t_{01},t_{10},t_{11} \in T$ be such that the table of $L$ is the $2\times 2$ array with these entries, and let $c\colon \{0,1\} \to T$. Then the rung element $\Delta(c) = \sum_{k}\sum_{k'} c_k\, t_{kk'}\, c_{k'}$ equals $c_0^2 t_{00} + c_0 c_1 (t_{01}+t_{10}) + c_1^2 t_{11}$.
--
--   This is the explicit expansion, in the two-leg case, of the quadratic form in the coefficient vector attached to a leg datum, the composition table playing the role of the Gram matrix; the off-diagonal entries occur only through their sum. It is used by [`IharaTower.exists_rungDatum_two`](thm.html#IharaTower.exists_rungDatum_two) in the construction of rungs for the Ihara-type tower.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_IharaTower_RungAssembly_deltaComb_two.lean

import Mathlib
import Definitions.Def_HeckeModule_IharaRungDatum

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IharaTower IharaTower.RungAssembly

theorem IharaTower.RungAssembly.deltaComb_two {𝒪 : Type} [CommRing 𝒪]
    {T : Type} [CommRing T] [Algebra 𝒪 T] {T' : Type} [CommRing T'] [Algebra 𝒪 T']
    {M : Type} [AddCommGroup M] [Module T M] [Module 𝒪 M] [IsScalarTower 𝒪 T M]
    {M' : Type} [AddCommGroup M'] [Module T' M'] [Module 𝒪 M'] [IsScalarTower 𝒪 T' M']
    {P : LevelPairing (𝒪 := 𝒪) T M} {P' : LevelPairing (𝒪 := 𝒪) T' M'}
    (L : LegDatum (𝒪 := 𝒪) P P' 2) (t₀₀ t₀₁ t₁₀ t₁₁ : T) (htab : L.table = ![![t₀₀, t₀₁], ![t₁₀, t₁₁]]) (c : Fin 2 → T) :
    deltaComb L c = c 0 ^ 2 * t₀₀ + c 0 * c 1 * (t₀₁ + t₁₀) + c 1 ^ 2 * t₁₁ := by sorry
