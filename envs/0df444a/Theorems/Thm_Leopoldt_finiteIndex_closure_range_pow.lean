-- Prove2me | Theorems.Thm_Leopoldt_finiteIndex_closure_range_pow
-- name    : Leopoldt.finiteIndex_closure_range_pow
-- status  : Proved
-- author  : @xuanji
-- created : 2026-09-27T22:57:24.956455+00:00
-- url     : https://prove2.me/theorems/0c501675-3768-4667-bd39-343f6ee96065
-- title:
--   Powers preserve the finite-index span of a finite family in a commutative group
-- statement:
--   Let a finite family $(g_i)$ in a commutative group $G$ generate a subgroup of finite index. For every positive integer $n$, the powers $(g_i^n)$ also generate a finite-index subgroup. Indeed, the first subgroup is finitely generated, and multiplication by $n$ has finite-index image in every finitely generated abelian group. This lemma preserves the finite-index condition of a Minkowski unit when it is raised to a power to enter a small $p$-adic logarithm ball.
-- source:
--   Elementary consequence of the structure theorem for finitely generated abelian groups, formalized in Mathlib as Subgroup.isFiniteRelIndex_map_powMonoidHom_of_fg. Applied to the Galois conjugates of a Minkowski unit in the Leopoldt mission (Preda Mihăilescu, On CM Z_p-extensions and the Leopoldt conjecture for CM fields, https://arxiv.org/abs/1105.4544, Section 1.1).

import Mathlib.GroupTheory.FiniteAbelian.Basic
import Mathlib.GroupTheory.Finiteness

namespace Leopoldt
theorem finiteIndex_closure_range_pow (G : Type*) [CommGroup G]
    (ι : Type*) [Finite ι] (f : ι → G)
    (h : (Subgroup.closure (Set.range f)).FiniteIndex)
    (n : ℕ) (hn : n ≠ 0) :
    (Subgroup.closure (Set.range fun i => f i ^ n)).FiniteIndex := by sorry
end Leopoldt
