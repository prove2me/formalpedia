-- Prove2me | Theorems.Thm_OAI_AsymptoticallyMinimalLittlewood_exists_same_code_far
-- name    : OAI.AsymptoticallyMinimalLittlewood.exists_same_code_far
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T04:41:51.116151+00:00
-- url     : https://prove2.me/theorems/65717b95-875b-4a07-8b5f-84ff5d1144f3
-- title:
--   Large families of sign vectors contain a far-apart pair with the same low-cost integer code
-- statement:
--   Let $K$ and $I$ be finite sets with $n=|K|$ and $m=|I|$ elements. For Boolean vectors $x,y\in\{\mathrm{true},\mathrm{false}\}^{K}$ let $d_H(x,y)=\#\{k\in K: x_k\neq y_k\}$ be their Hamming distance. Let $G$ be a finite set of Boolean vectors in $\{\mathrm{true},\mathrm{false}\}^K$, and let $\mathrm{code}\colon\{\mathrm{true},\mathrm{false}\}^K\to\mathbb{Z}^I$ be any map. Let $a,M$ be real numbers with $a\ge0$ and $e^{-a}\le\tfrac12$. Assume that every $x\in G$ has cost $\sum_{i\in I}|\mathrm{code}(x)_i|\le M$, and that
--
--   $$
--   |G|>\exp\Big(aM+4m\,e^{-a}+\frac{3n}{8}\Big).
--   $$
--
--   Then there are $x,y\in G$ with $\mathrm{code}(x)=\mathrm{code}(y)$ and $d_H(x,y)>n/16$.
--
--   This is the pigeonhole step of the entropy method for partial colorings: few codes are available (because their cost is bounded), each code class is confined to a small Hamming ball unless it contains a far pair, so a large enough family must contain two far-apart vectors with identical codes.
--
--   **Formalization Note** The map `code` is defined on all Boolean vectors but the cost bound is only assumed on $G$; the hypothesis $a\ge0$ follows from $e^{-a}\le\tfrac12$ but is stated separately.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/Littlewood/Rounding.lean#L293-L334

import Mathlib
import Definitions.Def_AsymptoticallyMinimalLittlewood
import Definitions.Def_OAI_Analysis_Littlewood_Gaussian
import Definitions.Def_OAI_Analysis_Littlewood_Rounding

open OAI OAI.AsymptoticallyMinimalLittlewood
universe u v w
open MeasureTheory Complex Real FourierTransform Filter Topology
open scoped FourierTransform SchwartzMap ContDiff

theorem OAI.AsymptoticallyMinimalLittlewood.exists_same_code_far {α : Type u} {β : Type v} [Fintype α] [DecidableEq α]
    [Fintype β] [DecidableEq β] (G : Finset (α → Bool))
    (code : (α → Bool) → β → ℤ) {a M : ℝ} (ha0 : 0 ≤ a)
    (ha : Real.exp (-a) ≤ 1 / 2)
    (hcost : ∀ x ∈ G, (∑ i, |(code x i : ℝ)|) ≤ M)
    (hlarge : Real.exp (a * M + 4 * Fintype.card β * Real.exp (-a) +
      3 * Fintype.card α / 8) < (G.card : ℝ)) :
    ∃ x ∈ G, ∃ y ∈ G, code x = code y ∧
      (Fintype.card α : ℝ) / 16 < (hammingDist x y : ℝ) := by sorry
