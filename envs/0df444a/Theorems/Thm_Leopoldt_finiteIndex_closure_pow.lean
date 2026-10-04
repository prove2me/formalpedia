-- Prove2me | Theorems.Thm_Leopoldt_finiteIndex_closure_pow
-- name    : Leopoldt.finiteIndex_closure_pow
-- status  : Proved
-- author  : @xuanji
-- created : 2026-09-27T23:07:55.326984+00:00
-- url     : https://prove2.me/theorems/5a759878-192a-4baa-b256-49a8741aca44
-- title:
--   Taking a positive common power preserves the rank of finite-index generators
-- statement:
--   Suppose a finite family $u_i$ generates a subgroup of finite index in a commutative group $G$. For every positive integer $n$, the family $u_i^n$ still generates a subgroup of finite index in $G$. This permits replacing global units by common positive powers, for example to put their local components in the convergence ball of the $p$-adic logarithm, while retaining full unit rank.
-- source:
--   Formal corollary of Mathlib.GroupTheory.FiniteAbelian.Basic, `Subgroup.isFiniteRelIndex_map_powMonoidHom_of_fg`, together with finite generation of the subgroup spanned by a finite family and transitivity of finite subgroup index.

import Mathlib.GroupTheory.FiniteAbelian.Basic
import Mathlib.GroupTheory.Finiteness
import Mathlib.GroupTheory.Index

theorem Leopoldt.finiteIndex_closure_pow {G : Type*} [CommGroup G]
    {ι : Type*} [Finite ι] (u : ι → G)
    (hu : (Subgroup.closure (Set.range u)).FiniteIndex) (n : ℕ) (hn : 0 < n) :
    (Subgroup.closure (Set.range fun i : ι => u i ^ n)).FiniteIndex := by sorry
