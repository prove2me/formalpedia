-- Prove2me | Theorems.Thm_OAI_ShortEgyptian_iterated_interval_vdc
-- name    : OAI.ShortEgyptian.iterated_interval_vdc
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T23:24:22.799029+00:00
-- url     : https://prove2.me/theorems/ef67576d-aead-472c-a25e-9f75a982bbc8
-- title:
--   Iterated van der Corput differencing down to $r$-fold differenced phases
-- statement:
--   Write $e(x)=e^{2\pi i x}$. For $h\in\mathbb{R}$ and $F:\mathbb{R}\to\mathbb{R}$ let $(D_hF)(x)=F(x)-F(x+h)$, and for a list $\mathbf h=(h_1,\dots,h_r)$ let $D_{\mathbf h}F=D_{h_1}\cdots D_{h_r}F$ (with $D_{\mathbf h}F=F$ for the empty list). For integers $p,q$ write $[p,q]=\{n\in\mathbb{Z}:p\le n\le q\}$, which is empty if $q<p$.
--
--   Let $r\in\mathbb{N}$, $f:\mathbb{R}\to\mathbb{R}$, $p,q\in\mathbb{Z}$, $L\in\mathbb{N}$ and $U,\varepsilon\in\mathbb{R}$, and assume
--   $$
--   L\ge1,\quad U>0,\quad L\le U,\quad \bigl|[p,q]\bigr|\le U,\quad 0\le\varepsilon\le1,\quad \frac1L\le\varepsilon^{2^r}.
--   $$
--   Suppose moreover that for every list $\mathbf h=(h_1,\dots,h_r)$ of $r$ integers with $1\le h_i<L$ for all $i$, the $r$-fold differenced sum is small:
--   $$
--   \Bigl|\sum_{n\in[p,\;q-(h_1+\cdots+h_r)]}e\bigl(D_{\mathbf h}f(n)\bigr)\Bigr|\le U\varepsilon^{2^r}.
--   $$
--   Then
--
--   $$
--   \Bigl|\sum_{n\in[p,q]}e\bigl(f(n)\bigr)\Bigr|\le4U\varepsilon .
--   $$
--
--   This packages $r$ successive applications of van der Corput's inequality. Each application squares the saving that has to be achieved, so a saving $\varepsilon$ in the original sum requires the saving $\varepsilon^{2^r}$ in every $r$-fold differenced sum. Those final sums can then be estimated by a second-derivative test.
--
--   **Formalization Note** The shifts are integers cast to reals, `backwardDifferences (hs.map (fun h : ℤ => (h : ℝ))) f n`, and the intervals are `Finset.Icc` in the integers.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/NumberTheory/ShortEgyptian/IteratedDifferencing.lean#L73-L139

import Mathlib
import Definitions.Def_ShortEgyptianFractions
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_Basic
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_FirstDerivative
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_ReciprocalDifferences
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_IntervalDifferencing
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_IteratedDifferencing

open OAI OAI.ShortEgyptian
open scoped BigOperators
open Finset

theorem OAI.ShortEgyptian.iterated_interval_vdc (r : ℕ) (f : ℝ → ℝ) (p q : ℤ)
    (L : ℕ) (U eps : ℝ) (hL : 1 ≤ L) (hU : 0 < U)
    (hLU : (L : ℝ) ≤ U) (hsize : ((Icc p q).card : ℝ) ≤ U)
    (heps : 0 ≤ eps) (heps1 : eps ≤ 1)
    (hLin : 1 / (L : ℝ) ≤ eps ^ (2 ^ r))
    (hleaf : ∀ hs : List ℤ, hs.length = r →
      (∀ h ∈ hs, 1 ≤ h ∧ h < L) →
      ‖∑ n ∈ Icc p (q - hs.sum),
        phase (backwardDifferences (hs.map (fun h : ℤ => (h : ℝ))) f n)‖ ≤
          U * eps ^ (2 ^ r)) :
    ‖∑ n ∈ Icc p q, phase (f n)‖ ≤ 4 * U * eps := by sorry
