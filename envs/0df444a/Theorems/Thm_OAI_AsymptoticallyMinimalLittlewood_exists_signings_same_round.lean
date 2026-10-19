-- Prove2me | Theorems.Thm_OAI_AsymptoticallyMinimalLittlewood_exists_signings_same_round
-- name    : OAI.AsymptoticallyMinimalLittlewood.exists_signings_same_round
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T04:43:53.885761+00:00
-- url     : https://prove2.me/theorems/b21975a5-6fca-4214-a72a-f7c072a4306c
-- title:
--   Two far-apart signings whose row sums round to the same integers at scale $64\sqrt{n\log(16m/n)}$
-- statement:
--   Let $K$ and $I$ be finite sets with $n=|K|$ and $m=|I|$ elements (columns and rows), and let $B=(B_{ik})_{i\in I,\,k\in K}$ be a real matrix with $|B_{ik}|\le1$ for all $i,k$. Assume $32\le n\le m$. Let $\sigma(\mathrm{true})=1$, $\sigma(\mathrm{false})=-1$, let $d_H$ denote Hamming distance on $\{\mathrm{true},\mathrm{false}\}^K$ (the number of coordinates where two vectors differ), let $\operatorname{round}(y)=\lfloor y+\tfrac12\rfloor$, and set
--
--   $$
--   d=64\sqrt{n\log\frac{16m}{n}}.
--   $$
--
--   Then there exist $x,y\in\{\mathrm{true},\mathrm{false}\}^K$ with $d_H(x,y)>n/16$ such that for every row $i\in I$
--
--   $$
--   \operatorname{round}\Big(\frac1d\sum_{k\in K}B_{ik}\,\sigma(x_k)\Big)=\operatorname{round}\Big(\frac1d\sum_{k\in K}B_{ik}\,\sigma(y_k)\Big).
--   $$
--
--   This is the entropy step of the partial-coloring method: since the rounded row sums of $x$ and $y$ agree, every row sum of the half-difference $\tfrac12(\sigma(x)-\sigma(y))$, a vector with entries in $\{-1,0,1\}$ and more than $n/16$ nonzero entries, is at most $d$ in absolute value.
--
--   **Formalization Note** Rows and columns are indexed by `Fintype`s $\beta$ and $\alpha$ with $n$ = `Fintype.card α`, $m$ = `Fintype.card β`, and the matrix is a function `B : β → α → ℝ`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/Littlewood/Rounding.lean#L418-L503

import Mathlib
import Definitions.Def_AsymptoticallyMinimalLittlewood
import Definitions.Def_OAI_Analysis_Littlewood_Gaussian
import Definitions.Def_OAI_Analysis_Littlewood_Rounding

open OAI OAI.AsymptoticallyMinimalLittlewood
universe u v w
open MeasureTheory Complex Real FourierTransform Filter Topology
open scoped FourierTransform SchwartzMap ContDiff

theorem OAI.AsymptoticallyMinimalLittlewood.exists_signings_same_round {α : Type u} {β : Type v} [Fintype α] [DecidableEq α]
    [Fintype β] [DecidableEq β] (B : β → α → ℝ)
    (hB : ∀ i k, |B i k| ≤ 1) (hs : 32 ≤ Fintype.card α)
    (hsR : Fintype.card α ≤ Fintype.card β) :
    let d := 64 * Real.sqrt ((Fintype.card α : ℝ) *
      Real.log (16 * Fintype.card β / Fintype.card α))
    ∃ x y : α → Bool, (Fintype.card α : ℝ) / 16 < (hammingDist x y : ℝ) ∧
      ∀ i, round ((∑ k, B i k * boolSign (x k)) / d) =
        round ((∑ k, B i k * boolSign (y k)) / d) := by sorry
