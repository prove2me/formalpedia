-- Prove2me | Theorems.Thm_Matrix_ProjGenLinGroup_exists_torsionFree_normal_subgroup_finiteIndex_of_fg_charZero
-- name    : Matrix.ProjGenLinGroup.exists_torsionFree_normal_subgroup_finiteIndex_of_fg_charZero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:11.33382+00:00
-- url     : https://prove2.me/theorems/7e3fc9e9-dbf6-58c0-94a2-b36f19c258d1
-- title:
--   Selberg's lemma for PGLₙ in characteristic zero
-- statement:
--   Let $K$ be a field of characteristic $0$ and let $n$ be a finite index type with decidable equality, so that $\mathrm{PGL}_n(K)$, the group `Matrix.ProjGenLinGroup n K` (the quotient of $\mathrm{GL}_n(K)$ by its centre), is defined. Let $\Gamma$ be a subgroup of $\mathrm{PGL}_n(K)$ that is finitely generated, i.e. $\Gamma$ is the closure of the image of a finite set. Then there exists a subgroup $N$ of $\mathrm{PGL}_n(K)$ with the following three properties: $N \le \Gamma$ and the subgroup $N \cap \Gamma$ of $\Gamma$ (i.e. `N.subgroupOf Γ`) is normal in $\Gamma$; the relative index of $N$ in $\Gamma$ is non-zero, which is the way finiteness of $[\Gamma : N]$ is expressed here; and every element $g \in N$ of finite order equals $1$, i.e. $N$ is torsion-free. Note that the torsion-freeness is asserted for all elements of $N$ as a subgroup of $\mathrm{PGL}_n(K)$, and normality is asserted relative to $\Gamma$ rather than in the whole group.
--
--   This is Selberg's lemma in its projective form: a finitely generated subgroup of $\mathrm{PGL}_n$ over a field of characteristic zero has a torsion-free normal subgroup of finite index. It is used in the Cerednik–Drinfeld part of the development, where a Schottky subgroup of finite index is extracted from a given arithmetic subgroup.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Matrix_ProjGenLinGroup_exists_torsionFree_normal_subgroup_finiteIndex_of_fg_charZero.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped MatrixGroups

theorem Matrix.ProjGenLinGroup.exists_torsionFree_normal_subgroup_finiteIndex_of_fg_charZero
    (K : Type) [Field K] [CharZero K] (n : Type) [Fintype n] [DecidableEq n]
    (Γ : Subgroup (Matrix.ProjGenLinGroup n K)) (hΓ : Γ.FG) :
    ∃ N : Subgroup (Matrix.ProjGenLinGroup n K), N ≤ Γ ∧ (N.subgroupOf Γ).Normal ∧ N.relIndex Γ ≠ 0 ∧
      ∀ g ∈ N, IsOfFinOrder g → g = 1 := by sorry
