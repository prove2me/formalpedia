-- Prove2me | Theorems.Thm_OAI_AsymptoticallyMinimalLittlewood_signing_exp_sum_le
-- name    : OAI.AsymptoticallyMinimalLittlewood.signing_exp_sum_le
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T04:31:39.908732+00:00
-- url     : https://prove2.me/theorems/edb3ef33-cd7c-4099-b98e-1a04463c034a
-- title:
--   Exponential moment bound for all signings of a bounded row
-- statement:
--   Let $K$ be a finite set with $n=|K|$ elements, let $\sigma\colon\{\mathrm{true},\mathrm{false}\}\to\{-1,1\}$ denote the sign encoding $\sigma(\mathrm{true})=1$, $\sigma(\mathrm{false})=-1$, and let $a\colon K\to\mathbb{R}$ satisfy $|a_k|\le 1$ for every $k\in K$. Then for every real $t$,
--
--   $$
--   \sum_{x\in\{\mathrm{true},\mathrm{false}\}^{K}}\exp\Big(t\sum_{k\in K}a_k\,\sigma(x_k)\Big)\le 2^{n}\,e^{t^{2}n/2}.
--   $$
--
--   Dividing by the number $2^n$ of signings, this says that for independent uniformly random signs $\varepsilon_k$ the moment generating function of $S=\sum_k a_k\varepsilon_k$ satisfies $\mathbb{E}\,e^{tS}\le e^{t^2 n/2}$, a Hoeffding-type sub-Gaussian bound stated with counting measure on the Boolean cube. It is the source of the exponential tail estimates for rounded row sums in the partial-coloring argument.
--
--   **Formalization Note** Signings are functions `x : α → Bool` and signs are `boolSign (x k)`; $n$ is `Fintype.card α`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/Littlewood/Rounding.lean#L34-L59

import Mathlib
import Definitions.Def_AsymptoticallyMinimalLittlewood
import Definitions.Def_OAI_Analysis_Littlewood_Gaussian
import Definitions.Def_OAI_Analysis_Littlewood_Rounding

open OAI OAI.AsymptoticallyMinimalLittlewood
universe u v w
open MeasureTheory Complex Real FourierTransform Filter Topology
open scoped FourierTransform SchwartzMap ContDiff

theorem OAI.AsymptoticallyMinimalLittlewood.signing_exp_sum_le {α : Type u} [Fintype α] [DecidableEq α] (a : α → ℝ)
    (ha : ∀ k, |a k| ≤ 1) (t : ℝ) :
    (∑ x : α → Bool, Real.exp (t * ∑ k, a k * boolSign (x k))) ≤
      2 ^ Fintype.card α * Real.exp (t ^ 2 * Fintype.card α / 2) := by sorry
