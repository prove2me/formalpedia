-- Prove2me | Theorems.Thm_OAI_AsymptoticallyMinimalLittlewood_exists_partial_coloring
-- name    : OAI.AsymptoticallyMinimalLittlewood.exists_partial_coloring
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T04:44:39.926701+00:00
-- url     : https://prove2.me/theorems/1beb9d7a-7249-46f2-82d9-af451f7432da
-- title:
--   Partial coloring of a bounded matrix with discrepancy $64\sqrt{n\log(16m/n)}$
-- statement:
--   Let $K$ and $I$ be finite sets with $n=|K|$ and $m=|I|$ elements (columns and rows), and let $B=(B_{ik})_{i\in I,\,k\in K}$ be a real matrix with $|B_{ik}|\le1$ for all $i,k$. Assume $1\le n\le m$. Then there is a vector $z\in\{-1,0,1\}^K$ such that at least $n/16$ of its coordinates are nonzero, i.e. $\#\{k: z_k\neq0\}\ge n/16$, and such that every row satisfies
--
--   $$
--   \Big|\sum_{k\in K}B_{ik}\,z_k\Big|\le64\sqrt{n\log\frac{16m}{n}}\qquad(i\in I).
--   $$
--
--   Such a $z$ is a partial coloring: it fixes a constant fraction of the coordinates to $\pm1$ while keeping all $m$ row sums within $O(\sqrt{n\log(m/n)})$. Iterating it on the uncolored coordinates, with geometrically shrinking error, produces a full $\pm1$ signing with the same order of discrepancy.
--
--   **Formalization Note** The vector $z$ is real-valued with each $z_k\in\{-1,0,1\}$, and the count of nonzero coordinates is compared with $n/16$ as a real number.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/Littlewood/Rounding.lean#L505-L584

import Mathlib
import Definitions.Def_AsymptoticallyMinimalLittlewood
import Definitions.Def_OAI_Analysis_Littlewood_Gaussian
import Definitions.Def_OAI_Analysis_Littlewood_Rounding

open OAI OAI.AsymptoticallyMinimalLittlewood
universe u v w
open MeasureTheory Complex Real FourierTransform Filter Topology
open scoped FourierTransform SchwartzMap ContDiff

theorem OAI.AsymptoticallyMinimalLittlewood.exists_partial_coloring {α : Type u} {β : Type v} [Fintype α] [DecidableEq α]
    [Fintype β] [DecidableEq β] (B : β → α → ℝ)
    (hB : ∀ i k, |B i k| ≤ 1) (hs : 0 < Fintype.card α)
    (hsR : Fintype.card α ≤ Fintype.card β) :
    ∃ z : α → ℝ, (∀ k, z k = -1 ∨ z k = 0 ∨ z k = 1) ∧
      (Fintype.card α : ℝ) / 16 ≤ ((Finset.univ.filter fun k ↦ z k ≠ 0).card : ℝ) ∧
      ∀ i, |∑ k, B i k * z k| ≤ 64 * Real.sqrt ((Fintype.card α : ℝ) *
        Real.log (16 * Fintype.card β / Fintype.card α)) := by sorry
