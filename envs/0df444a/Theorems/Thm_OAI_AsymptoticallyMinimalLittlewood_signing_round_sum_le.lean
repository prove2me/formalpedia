-- Prove2me | Theorems.Thm_OAI_AsymptoticallyMinimalLittlewood_signing_round_sum_le
-- name    : OAI.AsymptoticallyMinimalLittlewood.signing_round_sum_le
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T04:33:07.039604+00:00
-- url     : https://prove2.me/theorems/79980e1c-d328-416a-b294-df21105056df
-- title:
--   Average rounding cost of a randomly signed bounded row
-- statement:
--   Let $K$ be a finite set with $n=|K|$ elements, let $\sigma\colon\{\mathrm{true},\mathrm{false}\}\to\{-1,1\}$ denote the sign encoding $\sigma(\mathrm{true})=1$, $\sigma(\mathrm{false})=-1$, and let $a\colon K\to\mathbb{R}$ satisfy $|a_k|\le1$ for all $k$. Let $d,t$ be real numbers with $d>0$, $t\ge0$ and $td\ge4$, and let $\operatorname{round}(y)=\lfloor y+\tfrac12\rfloor$ be rounding to the nearest integer. Then
--
--   $$
--   \sum_{x\in\{\mathrm{true},\mathrm{false}\}^{K}}\left|\operatorname{round}\Big(\frac1d\sum_{k\in K}a_k\,\sigma(x_k)\Big)\right|\le 2^{n}\cdot 2\exp\Big(\frac{t^{2}n}{2}-\frac{td}{4}\Big).
--   $$
--
--   In probabilistic terms: if the signs are chosen uniformly at random, the expected absolute value of the signed row sum rounded at scale $d$ is at most $2e^{t^2n/2-td/4}$. With $d$ a large multiple of $\sqrt{n}$ and $t$ of order $d/n$ this is tiny, which is what makes most signings have small total rounding cost over all rows in the partial-coloring argument.
--
--   **Formalization Note** Signings are functions `x : α → Bool` with signs `boolSign (x k)`, and the bound is stated as a sum over all $2^n$ signings (counting measure).
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/Littlewood/Rounding.lean#L101-L127

import Mathlib
import Definitions.Def_AsymptoticallyMinimalLittlewood
import Definitions.Def_OAI_Analysis_Littlewood_Gaussian
import Definitions.Def_OAI_Analysis_Littlewood_Rounding

open OAI OAI.AsymptoticallyMinimalLittlewood
universe u v w
open MeasureTheory Complex Real FourierTransform Filter Topology
open scoped FourierTransform SchwartzMap ContDiff

theorem OAI.AsymptoticallyMinimalLittlewood.signing_round_sum_le {α : Type u} [Fintype α] [DecidableEq α] (a : α → ℝ)
    (ha : ∀ k, |a k| ≤ 1) {d t : ℝ} (hd : 0 < d) (ht : 0 ≤ t)
    (htd : 4 ≤ t * d) :
    (∑ x : α → Bool, |(round ((∑ k, a k * boolSign (x k)) / d) : ℝ)|) ≤
      2 ^ Fintype.card α * (2 * Real.exp (t ^ 2 * Fintype.card α / 2 - t * d / 4)) := by sorry
