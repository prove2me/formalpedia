-- Prove2me | Theorems.Thm_LocalGL2_cartanDiag_cartanRel_iff
-- name    : LocalGL2.cartanDiag_cartanRel_iff
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:11.015121+00:00
-- url     : https://prove2.me/theorems/bccdb272-c622-580a-8062-336da8b1d27a
-- title:
--   Uniqueness of ordered Cartan representatives for 2×2 matrices
-- statement:
--   Let $R$ be a commutative domain which is a discrete valuation ring, let $\varpi \in R$ be irreducible, and let $a,b,a',b'$ be natural numbers with $a \le b$ and $a' \le b'$. Write $\mathrm{cartanDiag}\,\varpi\,a\,b$ for the diagonal matrix $!!\,[\varpi^a,0;0,\varpi^b]$ in $\mathrm{Mat}_2(R)$, and let $\mathrm{CartanRel}\,g\,h$ mean that there exist units $k_1,k_2$ of the ring $\mathrm{Mat}_2(R)$ with $g = k_1 h k_2$. The theorem asserts the equivalence: the matrices $\mathrm{diag}(\varpi^a,\varpi^b)$ and $\mathrm{diag}(\varpi^{a'},\varpi^{b'})$ are related in this two-sided sense, i.e. lie in the same double coset for the group of invertible $2\times2$ matrices over $R$ acting on both sides, if and only if $a = a'$ and $b = b'$. Thus, among ordered exponent pairs, the diagonal representative of a double coset is unique; no nondegeneracy hypothesis on the matrices is needed, the case $\varpi^a = \varpi^b = 0$ being excluded by $\varpi$ being irreducible in a domain.
--
--   This is the uniqueness half of the Cartan decomposition for $\mathrm{GL}_2$ over a discrete valuation ring, equivalently uniqueness of elementary divisors (Smith normal form) in rank $2$. It is what makes the indexing of double cosets by ordered exponent pairs well defined, and is used downstream in the construction of the local spherical Hecke algebra, for instance in [`LocalGL2.existsUnique_mem_doubleCoset_zpow`](thm.html#LocalGL2.existsUnique_mem_doubleCoset_zpow), [`LocalGL2.exists_basis_heckeIndicator_zpow`](thm.html#LocalGL2.exists_basis_heckeIndicator_zpow) and [`LocalGL2.existsUnique_algHom_heckeIndicator_eq`](thm.html#LocalGL2.existsUnique_algHom_heckeIndicator_eq).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LocalGL2_cartanDiag_cartanRel_iff.lean

import Mathlib
import Definitions.Def_LocalLanglands_CartanDecomposition

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open Matrix LocalGL2

theorem LocalGL2.cartanDiag_cartanRel_iff
    {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {ϖ : R} (hϖ : Irreducible ϖ) {a b a' b' : ℕ}
    (hab : a ≤ b) (hab' : a' ≤ b') :
    CartanRel (cartanDiag ϖ a b) (cartanDiag ϖ a' b') ↔ a = a' ∧ b = b' := by sorry
