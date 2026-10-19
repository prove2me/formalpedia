-- Prove2me | Theorems.Thm_OAI_AsymptoticallyMinimalLittlewood_hamming_exp_sum
-- name    : OAI.AsymptoticallyMinimalLittlewood.hamming_exp_sum
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T04:38:38.968315+00:00
-- url     : https://prove2.me/theorems/2efd30bb-7bc1-433f-86bd-d68d88377176
-- title:
--   Partition function of the Hamming distance on the Boolean cube
-- statement:
--   Let $K$ be a finite set with $n=|K|$ elements. For Boolean vectors $x,y\in\{\mathrm{true},\mathrm{false}\}^{K}$ let $d_H(x,y)=\#\{k\in K: x_k\neq y_k\}$ be their Hamming distance. Then for every fixed $x\in\{\mathrm{true},\mathrm{false}\}^K$ and every real $a$,
--
--   $$
--   \sum_{y\in\{\mathrm{true},\mathrm{false}\}^{K}}e^{-a\,d_H(x,y)}=\big(1+e^{-a}\big)^{n}.
--   $$
--
--   Grouping by distance this is the binomial identity $\sum_{j}\binom{n}{j}e^{-aj}=(1+e^{-a})^n$. It is the exponential-moment tool used to bound the size of Hamming balls.
--
--   **Formalization Note** Boolean vectors are functions `α → Bool` and $d_H$ is Mathlib's `hammingDist`, cast to $\mathbb{R}$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/Littlewood/Rounding.lean#L211-L226

import Mathlib
import Definitions.Def_AsymptoticallyMinimalLittlewood
import Definitions.Def_OAI_Analysis_Littlewood_Gaussian
import Definitions.Def_OAI_Analysis_Littlewood_Rounding

open OAI OAI.AsymptoticallyMinimalLittlewood
universe u v w
open MeasureTheory Complex Real FourierTransform Filter Topology
open scoped FourierTransform SchwartzMap ContDiff

theorem OAI.AsymptoticallyMinimalLittlewood.hamming_exp_sum {α : Type u} [Fintype α] [DecidableEq α]
    (x : α → Bool) (a : ℝ) :
    (∑ y : α → Bool, Real.exp (-a * hammingDist x y)) =
      (1 + Real.exp (-a)) ^ Fintype.card α := by sorry
