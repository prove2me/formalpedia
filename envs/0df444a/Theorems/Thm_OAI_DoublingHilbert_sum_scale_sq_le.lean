-- Prove2me | Theorems.Thm_OAI_DoublingHilbert_sum_scale_sq_le
-- name    : OAI.DoublingHilbert.sum_scale_sq_le
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-14T22:20:21.723608+00:00
-- url     : https://prove2.me/theorems/baf56c94-2939-4645-83db-f7a99335b6b1
-- title:
--   Geometric tail bound $\sum_{j\in s} r_j^2\le 2R^2$ for the scales $r_j=1000^{-(j+1)}$
-- statement:
--   Let $r_j=1000^{-(j+1)}$ for $j\in\mathbb{N}$ be the scales of the strip construction.
--
--   **Theorem.** Let $s\subseteq\mathbb{N}$ be a finite set and let $R\ge0$ be a real number such that $r_j\le R$ for every $j\in s$. Then
--   $$
--   \sum_{j\in s}r_j^2\le 2R^2 .
--   $$
--
--   Because consecutive scales differ by the factor $1000$, a finite family of scales all bounded by $R$ has total squared size comparable to the largest one; the constant $2$ is deliberately coarse. In the doubling estimate for the strip set this bounds the contribution of all fine levels (those with $r_j\le t/64$) to a squared distance by $2\cdot 2(t/64)^2=t^2/1024$.
--
--   **Formalization Note** The scale is `scale j`, defined as the $(j+1)$-st power of $1/1000$; the statement includes the case $s=\emptyset$, where the left side is the empty sum $0$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/DoublingHilbert/Construction.lean#L381-L417

import Mathlib
import Definitions.Def_DoublingHilbert
import Definitions.Def_OAI_Geometry_DoublingHilbert_Construction

open OAI OAI.DoublingHilbert
open scoped BigOperators
open Set

theorem OAI.DoublingHilbert.sum_scale_sq_le {s : Finset ℕ} {R : ℝ} (hR : 0 ≤ R)
    (hs : ∀ j ∈ s, scale j ≤ R) : ∑ j ∈ s, (scale j) ^ 2 ≤ 2 * R ^ 2 := by sorry
