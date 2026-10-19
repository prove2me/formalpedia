-- Prove2me | Theorems.Thm_OAI_AsymptoticallyMinimalLittlewood_card_good_cost
-- name    : OAI.AsymptoticallyMinimalLittlewood.card_good_cost
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T04:40:50.422336+00:00
-- url     : https://prove2.me/theorems/2ebf57d9-821c-4b45-836c-a7a4ac4be6b4
-- title:
--   A nonnegative cost with average at most $M/2$ is at most $M$ on half of a finite set
-- statement:
--   Let $\Gamma$ be a finite set, let $f\colon\Gamma\to\mathbb{R}$ satisfy $f(x)\ge0$ for all $x$, and let $M>0$. If
--
--   $$
--   \sum_{x\in\Gamma}f(x)\le\frac{|\Gamma|\,M}{2},
--   $$
--
--   then the set $\{x\in\Gamma: f(x)\le M\}$ has at least $|\Gamma|/2$ elements.
--
--   This is the counting form of Markov's inequality: if the average of a nonnegative quantity is at most $M/2$, then at most half of the points have $f>M$. In the partial-coloring argument it shows that at least half of all signings have small total rounding cost.
--
--   **Formalization Note** $\Gamma$ is a `Fintype` and the good set is `Finset.univ.filter (fun x => f x ≤ M)`; cardinalities are compared as real numbers.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/Littlewood/Rounding.lean#L270-L291

import Mathlib
import Definitions.Def_AsymptoticallyMinimalLittlewood
import Definitions.Def_OAI_Analysis_Littlewood_Gaussian
import Definitions.Def_OAI_Analysis_Littlewood_Rounding

open OAI OAI.AsymptoticallyMinimalLittlewood
universe u v w
open MeasureTheory Complex Real FourierTransform Filter Topology
open scoped FourierTransform SchwartzMap ContDiff

theorem OAI.AsymptoticallyMinimalLittlewood.card_good_cost {γ : Type w} [Fintype γ] [DecidableEq γ]
    (f : γ → ℝ) (hf : ∀ x, 0 ≤ f x) {M : ℝ} (hM : 0 < M)
    (hsum : (∑ x, f x) ≤ (Fintype.card γ : ℝ) * M / 2) :
    (Fintype.card γ : ℝ) / 2 ≤ ((Finset.univ.filter fun x ↦ f x ≤ M).card : ℝ) := by sorry
