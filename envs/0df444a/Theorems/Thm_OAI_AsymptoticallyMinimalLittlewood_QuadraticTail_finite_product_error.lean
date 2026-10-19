-- Prove2me | Theorems.Thm_OAI_AsymptoticallyMinimalLittlewood_QuadraticTail_finite_product_error
-- name    : OAI.AsymptoticallyMinimalLittlewood.QuadraticTail.finite_product_error
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T05:09:18.762752+00:00
-- url     : https://prove2.me/theorems/6ea69234-1102-4002-9fa4-6fc5fc6baeaa
-- title:
--   Finite products of $O(1/T)$-approximations by functions bounded by one are $O(1/T)$-approximations
-- statement:
--   Let $I$ and $Z$ be arbitrary sets, let $S\subseteq I$ be a finite subset, and for each $i\in I$ let $f_i,h_i:\mathbb{R}\times Z\to\mathbb{C}$ be functions of a real parameter $T$ and a point $z\in Z$. Assume:
--
--   1. $|h_i(T,z)|\le1$ for every $i\in S$, every real $T$ and every $z\in Z$;
--   2. for every $i\in S$ there is a constant $C_i\ge0$ such that $|f_i(T,z)-h_i(T,z)|\le C_i/T$ for all real $T\ge1$ and all $z\in Z$.
--
--   Then there is a constant $C\ge0$ such that for every real $T\ge1$ and every $z\in Z$,
--
--   $$
--   \Bigl|\prod_{i\in S}f_i(T,z)-\prod_{i\in S}h_i(T,z)\Bigr|\le\frac{C}{T}.
--   $$
--
--   A product of finitely many factors, each approximated uniformly at rate $O(1/T)$ by functions of modulus at most one, is thus approximated at the same rate; both the approximations and the targets may depend on $T$. The lemma converts one-dimensional truncation estimates for chirps into estimates for their tensor products over several variables.
--
--   **Formalization Note** The functions are curried, $f, h : I \to \mathbb{R}\to Z\to\mathbb{C}$, and the index types live in arbitrary universes.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/Littlewood/QuadraticTail.lean#L540-L581

import Mathlib
import Definitions.Def_AsymptoticallyMinimalLittlewood
import Definitions.Def_OAI_Analysis_Littlewood_Gaussian
import Definitions.Def_OAI_Analysis_Littlewood_Rounding
import Definitions.Def_OAI_Analysis_Littlewood_BinaryPacket
import Definitions.Def_OAI_Analysis_Littlewood_QuadraticTail

open OAI OAI.AsymptoticallyMinimalLittlewood OAI.AsymptoticallyMinimalLittlewood.QuadraticTail
universe uI uZ
open MeasureTheory Filter Topology Complex
open scoped BigOperators ContDiff

theorem OAI.AsymptoticallyMinimalLittlewood.QuadraticTail.finite_product_error {I : Type uI} {Z : Type uZ} (S : Finset I)
    (f h : I → ℝ → Z → ℂ)
    (hh : ∀ i ∈ S, ∀ T z, ‖h i T z‖≤1)
    (hf : ∀ i ∈ S, ∃ C : ℝ, 0≤C ∧ ∀ T, 1≤T → ∀ z, ‖f i T z-h i T z‖≤C/T) :
    ∃ C : ℝ, 0≤C ∧ ∀ T, 1≤T → ∀ z,
      ‖(∏ i ∈ S, f i T z)-(∏ i ∈ S, h i T z)‖ ≤ C/T := by sorry
