-- Prove2me | Theorems.Thm_OAI_ShortEgyptian_reciprocal_leaf_sqrt
-- name    : OAI.ShortEgyptian.reciprocal_leaf_sqrt
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T23:26:08.78241+00:00
-- url     : https://prove2.me/theorems/f8a93caf-b4ff-4514-af46-4e7f9ce272fc
-- title:
--   Second-derivative bound for exponential sums of iterated differences of $Z/x$
-- statement:
--   Write $e(x)=e^{2\pi i x}$, and for a list $\mathbf h=(h_1,\dots,h_k)$ of real numbers let $D_{\mathbf h}F=D_{h_1}\cdots D_{h_k}F$, where $(D_hF)(x)=F(x)-F(x+h)$ (with $D_{\mathbf h}F=F$ for the empty list).
--
--   Let $\mathbf h=(h_1,\dots,h_k)$ be a list with all $h_i\ge0$, and put $S=h_1+\cdots+h_k$ and $P=h_1\cdots h_k$. Let $Z,U\in\mathbb{R}$ and $p,q\in\mathbb{Z}$ with
--   $$
--   Z\ge0,\qquad U\ge1,\qquad U\le p\le q,\qquad q+S\le2U,
--   $$
--   let
--   $$
--   \lambda=Z\,P\,(k+2)!\,\Bigl(\frac1{3U}\Bigr)^{k+3},
--   $$
--   and assume $0<\lambda\le1$. Then the iterated difference $g=D_{\mathbf h}(x\mapsto Z/x)$ satisfies
--
--   $$
--   \Bigl|\sum_{n=p}^{q}e\bigl(g(n)\bigr)\Bigr|\le6\cdot3^{k+3}\,U\sqrt\lambda+\frac6{\sqrt\lambda}+6 .
--   $$
--
--   This is the estimate for the final sums produced by van der Corput differencing when the phase is $Z/n$ and $n$ ranges over part of $[U,2U]$. The parameter $\lambda$ measures the size of the second differences of the differenced phase $g$.
--
--   **Formalization Note** $D_{\mathbf h}$ is `backwardDifferences hs`, and $\lambda$ is a variable together with its defining equation as a hypothesis, in the form `Z * (hs.prod * (hs.length + 2).factorial * (1 / (3 * U)) ^ (hs.length + 3))`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/NumberTheory/ShortEgyptian/ReciprocalEstimates.lean#L10-L84

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

theorem OAI.ShortEgyptian.reciprocal_leaf_sqrt (hs : List ℝ) (hhs : ∀ h ∈ hs, 0 ≤ h)
    (Z U : ℝ) (p q : ℤ) (hZ : 0 ≤ Z) (hU : 1 ≤ U)
    (hp : U ≤ p) (hq : (q : ℝ) + hs.sum ≤ 2 * U) (hpq : p ≤ q)
    (lam : ℝ) (hlamdef : lam =
      Z * (hs.prod * (hs.length + 2).factorial * (1 / (3 * U)) ^ (hs.length + 3)))
    (hlam : 0 < lam) (hlam1 : lam ≤ 1) :
    ‖∑ n ∈ Icc p q, phase (backwardDifferences hs (fun x => Z / x) n)‖ ≤
      6 * (3 : ℝ) ^ (hs.length + 3) * U * Real.sqrt lam + 6 / Real.sqrt lam + 6 := by sorry
