-- Prove2me | Theorems.Thm_Milnor_exists_le_growthFunction_of_isSolvable_of_not_isPolycyclic
-- name    : Milnor.exists_le_growthFunction_of_isSolvable_of_not_isPolycyclic
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-09-19T22:31:37.922988+00:00
-- url     : https://prove2.me/theorems/24cd7760-a442-439f-8b71-ae239df5b65e
-- title:
--   Theorem: a solvable group which is not polycyclic has exponential growth
-- statement:
--   Let $\Gamma$ be a solvable group which is not polycyclic and $S$ a finite generating
--   set of $\Gamma$. Then there is a constant $c > 1$ with $g_S(m) \ge c^m$ for every integer
--   $m \ge 1$, where $g_S(m)$ is the number of elements of $\Gamma$ expressible as words of length at
--   most $m$ in $S$ and $S^{-1}$.
-- source:
--   Milnor, J., Growth of finitely generated solvable groups, Journal of Differential Geometry 2 (1968) 447–449, https://doi.org/10.4310/jdg/1214428659, Theorem, p. 447

import Definitions.Def_MilnorWolf_Growth
import Mathlib

namespace Milnor

/-- Milnor's Theorem (p. 447): let `Γ` be a solvable group which is not polycyclic, and `S` a
finite set of generators for `Γ`; then there exists an exponential lower bound
`g_S(m) ≥ (constant)^m > 1` for the growth function `g_S` of `Γ`. -/
theorem exists_le_growthFunction_of_isSolvable_of_not_isPolycyclic {Γ : Type*} [Group Γ]
    [Group.IsSolvable Γ] (hnp : ¬ MilnorWolf.IsPolycyclic Γ) (S : Finset Γ)
    (hS : Subgroup.closure (S : Set Γ) = ⊤) :
    ∃ c : ℝ, 1 < c ∧ ∀ m : ℕ, 1 ≤ m → c ^ m ≤ (MilnorWolf.growthFunction S m : ℝ) := by
  sorry

end Milnor
