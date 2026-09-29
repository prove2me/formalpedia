-- Prove2me | Theorems.Thm_LT_LatticeTree_eq_of_le_of_hasDetIndex_padic
-- name    : LT.LatticeTree.eq_of_le_of_hasDetIndex_padic
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:00.858323+00:00
-- url     : https://prove2.me/theorems/bb1d8623-e793-594c-a955-ac32089b7371
-- title:
--   Nested ℤₚ-lattices of equal determinant index coincide
-- statement:
--   Let $p$ be a prime and consider submodules $N \le N'$ of $\mathbb{Q}_p^2 = (\mathrm{Fin}\,2 \to \mathbb{Q}_p)$ over $\mathbb{Z}_p$. Fix an integer $e$ and assume that both $N$ and $N'$ satisfy `HasDetIndex` with respect to the element $p \in \mathbb{Z}_p$ and this same $e$; by the definition of that predicate this means: there is $g \in \mathrm{GL}_2(\mathbb{Q}_p)$ with $N$ the image of the standard lattice $\mathrm{stdLattice}\,\mathbb{Z}_p\,\mathbb{Q}_p$ (the submodule of vectors all of whose coordinates lie in the image of $\mathbb{Z}_p$) under the map $v \mapsto g\,v$, together with a unit $u \in \mathbb{Z}_p^{\times}$ such that $\det g = u\,p^{e}$ in $\mathbb{Q}_p$ (the $e$-th power being taken in the group of units of $\mathbb{Q}_p$), and likewise $N'$ is the image of the standard lattice under some $g' \in \mathrm{GL}_2(\mathbb{Q}_p)$ with $\det g' = u'\,p^{e}$ for some $u' \in \mathbb{Z}_p^{\times}$. The conclusion is $N = N'$: two nested lattices of the form $g\,\mathbb{Z}_p^2$ whose determinants have the same $p$-valuation up to a unit are equal.
--
--   An elementary lemma on the lattice tree of $\mathbb{Q}_p^2$: within a chain $N \le N'$ the determinant index $e$ determines the lattice. It is used in the Čerednik–Drinfeld part of the development, where transported lattices attached to a Cartier/Drinfeld quadruple are shown to agree once their indices match.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LT_LatticeTree_eq_of_le_of_hasDetIndex_padic.lean

import Mathlib
import Definitions.Def_CerednikDrinfeld_DrinfeldQuadruple
import Definitions.Def_CerednikDrinfeld_DrinfeldQuadrupleRelations

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CerednikDrinfeld CerednikDrinfeld.FormalOmega LT.LatticeTree

open scoped PadicInt Padic

theorem LT.LatticeTree.eq_of_le_of_hasDetIndex_padic
    (p : ℕ) [Fact p.Prime] (N N' : Submodule ℤ_[p] (Fin 2 → ℚ_[p])) (hle : N ≤ N') (e : ℤ)
    (hN : HasDetIndex (K := ℚ_[p]) (p : ℤ_[p]) N e) (hN' : HasDetIndex (K := ℚ_[p]) (p : ℤ_[p]) N' e) :
    N = N' := by sorry
