-- Prove2me | Theorems.Thm_Monoid_CoprodI_nonempty_freeGroupBasis_fin_kuroshRank
-- name    : Monoid.CoprodI.nonempty_freeGroupBasis_fin_kuroshRank
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:55.856965+00:00
-- url     : https://prove2.me/theorems/3fb03155-d2bb-5679-be6d-64f799195868
-- title:
--   Freeness of torsion-free finite-index subgroups of G₀ * G₁
-- statement:
--   Let $G : \mathrm{Fin}\,2 \to \mathrm{Type}$ be a pair of finite groups $G_0, G_1$, and let $\mathrm{CoprodI}\,G = G_0 * G_1$ be their free product, with canonical injections `Monoid.CoprodI.of`. Let $H$ be a subgroup of $G_0 * G_1$ of finite index, and assume that for every $i \in \{0,1\}$, every $g \in G_0 * G_1$ and every $x \in G_i$, the relation $g^{-1}\,\iota_i(x)\,g \in H$ forces $x = 1$; that is, no conjugate of a nontrivial element of either free factor lies in $H$. The conclusion asserts that the type of free group bases of $H$ indexed by $\mathrm{Fin}\bigl(1 + m - m/\lvert G_0\rvert - m/\lvert G_1\rvert\bigr)$ is nonempty, where $m = [G_0 * G_1 : H]$ is the index as a natural number and the subtractions and divisions are those of $\mathbb{N}$ (truncated subtraction, integer division; in fact $\lvert G_i\rvert$ divides $m$ under the stated hypothesis). Thus $H$ is a free group admitting a free basis of exactly that finite cardinality, i.e. of rank equal to $1 + m - m/\lvert G_0\rvert - m/\lvert G_1\rvert$.
--
--   This is the Kurosh/Nielsen–Schreier statement for a free product of two finite groups, in the Bass–Serre form: the hypothesis says precisely that $H$ acts freely on the tree of cosets of the two factors, whence $H$ is free, and the rank is the first Betti number of the quotient graph, with $m/\lvert G_0\rvert + m/\lvert G_1\rvert$ vertices and $m$ edges. It is used to produce free subgroups of $\mathrm{PSL}_2$ from trace conditions, in [`Matrix.SpecialLinearGroup.nonempty_freeGroupBasis_map_quotient_center_of_forall_trace_ne`](thm.html#Matrix.SpecialLinearGroup.nonempty_freeGroupBasis_map_quotient_center_of_forall_trace_ne).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Monoid_CoprodI_nonempty_freeGroupBasis_fin_kuroshRank.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem Monoid.CoprodI.nonempty_freeGroupBasis_fin_kuroshRank {G : Fin 2 → Type*} [∀ i, Group (G i)] [∀ i, Finite (G i)]
    (H : Subgroup (Monoid.CoprodI G)) [H.FiniteIndex]
    (hH : ∀ (i : Fin 2) (g : Monoid.CoprodI G) (x : G i), g⁻¹ * Monoid.CoprodI.of x * g ∈ H → x = 1) :
    Nonempty (FreeGroupBasis
      (Fin (1 + H.index - H.index / Nat.card (G 0) - H.index / Nat.card (G 1))) H) := by sorry
