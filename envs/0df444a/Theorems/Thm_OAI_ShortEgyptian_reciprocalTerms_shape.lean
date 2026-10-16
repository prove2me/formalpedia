-- Prove2me | Theorems.Thm_OAI_ShortEgyptian_reciprocalTerms_shape
-- name    : OAI.ShortEgyptian.reciprocalTerms_shape
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T23:21:05.304142+00:00
-- url     : https://prove2.me/theorems/ea0716fb-cfd7-442f-b286-c95594e329dd
-- title:
--   Number and size of the shift lists in the expansion of iterated differences of $1/x$
-- statement:
--   For a real number $h$ and a finite list $\mathbf a=(a_1,\dots,a_m)$ of real numbers, let $E_h(\mathbf a)$ be the list of the $m$ lists
--   $$
--   \mathbf a^{(i)}=(a_1,\dots,a_i,\;a_i+h,\;a_{i+1}+h,\dots,a_m+h)\qquad(i=1,\dots,m),
--   $$
--   each of length $m+1$ (so $E_h$ of the empty list is empty). These lists come from the telescoping identity $\prod_{j}\frac1{x+a_j}-\prod_{j}\frac1{x+h+a_j}=h\sum_{i=1}^m\prod_{b\in\mathbf a^{(i)}}\frac1{x+b}$, valid whenever no denominator vanishes. For a list $\mathbf h=(h_1,\dots,h_k)$ of real numbers define the list of lists $R(\mathbf h)$ recursively: $R$ of the empty list is the one-element list $\bigl((0)\bigr)$, and $R(h_1,h_2,\dots,h_k)$ is the concatenation, in order, of the lists $E_{h_1}(\mathbf a)$ over all members $\mathbf a$ of $R(h_2,\dots,h_k)$.
--
--   Let $\mathbf h=(h_1,\dots,h_k)$ be a list of real numbers with $h_i\ge0$ for every $i$. Then:
--
--   1. $R(\mathbf h)$ has exactly $k!$ members (counted with multiplicity);
--   2. every member $\mathbf a$ of $R(\mathbf h)$ has length $k+1$, and every entry $a$ of $\mathbf a$ satisfies
--
--   $$
--   0\le a\le h_1+h_2+\cdots+h_k .
--   $$
--
--   The lists in $R(\mathbf h)$ index an exact expansion of the iterated difference $D_{h_1}\cdots D_{h_k}(1/x)$, where $(D_hF)(x)=F(x)-F(x+h)$, as $h_1\cdots h_k$ times a sum of products of $k+1$ reciprocals $1/(x+a)$. The theorem supplies the two facts needed to bound that expansion from above and below: the number of terms and the range of the shifts $a$.
--
--   **Formalization Note** $E_h$ is `expandDifference h` and $R$ is `reciprocalTerms`, both producing Lean lists, so repeated lists are counted separately; the count is `(reciprocalTerms hs).length = hs.length.factorial`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/NumberTheory/ShortEgyptian/ReciprocalDifferences.lean#L92-L118

import Mathlib
import Definitions.Def_ShortEgyptianFractions
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_Basic
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_FirstDerivative
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_ReciprocalDifferences

open OAI OAI.ShortEgyptian
open scoped BigOperators
open Finset

theorem OAI.ShortEgyptian.reciprocalTerms_shape (hs : List ℝ) (hhs : ∀ h ∈ hs, 0 ≤ h) :
    (reciprocalTerms hs).length = hs.length.factorial ∧
      ∀ as ∈ reciprocalTerms hs,
        as.length = hs.length + 1 ∧ ∀ a ∈ as, 0 ≤ a ∧ a ≤ hs.sum := by sorry
