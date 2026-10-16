-- Prove2me | Theorems.Thm_OAI_CliqueFreeIndependence_FiniteEntropy_entropy_supported_concentration
-- name    : OAI.CliqueFreeIndependence.FiniteEntropy.entropy_supported_concentration
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T21:27:03.192822+00:00
-- url     : https://prove2.me/theorems/7dfb63ee-98de-4597-b425-ffc16069b8ef
-- title:
--   Weighted entropy of a law concentrated on a light set is at most about $\log m$
-- statement:
--   For a finite index set $I$, a weight vector $w=(w_i)_{i\in I}$ and a vector $p=(p_i)_{i\in I}$, the weighted entropy is
--   $H_w(p)=\sum_{i\in I}p_i\log\frac{w_i}{p_i}$, with the convention that terms with $p_i=0$ vanish ($\log$ is the natural logarithm). A probability vector is a vector with $p_i\ge0$ for all $i$ and $\sum_ip_i=1$. For $w\equiv1$, $H_w(p)$ is the Shannon entropy of $p$, and in general $H_w(p)=H(p)+\sum_ip_i\log w_i$.
--
--   Let $s\subseteq D\subseteq I$, let $w_i>0$ for every $i\in D$, and let $p$ be a probability vector on $I$ supported in $D$ (that is, $p_i=0$ for $i\notin D$). Let $m\ge1$ and $M>0$ be real numbers with
--   $\sum_{i\in s}w_i\le m$ and $\sum_{i\in D}w_i\le M$. Then
--
--   $$
--   H_w(p)\le\log2+\log m+\Bigl(1-\sum_{i\in s}p_i\Bigr)\log M .
--   $$
--
--   So if $p$ puts most of its mass on a set $s$ of small total weight $m$, its weighted entropy is essentially at most $\log m$: only the mass $1-p(s)$ outside $s$ pays the larger price $\log M$, and the cost of not knowing whether the outcome lies in $s$ is at most $\log 2$. Read contrapositively, a large weighted entropy forces $p$ to put substantial mass outside every light set $s$; this is the form in which the inequality is used for random-walk laws.
--
--   **Formalization Note** The weighted entropy is `entropy w p = ∑ i, p i * Real.log (w i / p i)`; $s$ and $D$ are `Finset I` with $s\subseteq D$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/CliqueFree/FiniteEntropy.lean#L293-L328

import Mathlib
import Definitions.Def_CliqueFreeLog
import Definitions.Def_OAI_Combinatorics_CliqueFree_Numerical
import Definitions.Def_OAI_Combinatorics_CliqueFree_WeightedGraph
import Definitions.Def_OAI_Combinatorics_CliqueFree_Optimizer
import Definitions.Def_OAI_Combinatorics_CliqueFree_Lottery
import Definitions.Def_OAI_Combinatorics_CliqueFree_MultiplierLaw
import Definitions.Def_OAI_Combinatorics_CliqueFree_Deletion
import Definitions.Def_OAI_Combinatorics_CliqueFree_FiniteEntropy

open OAI OAI.CliqueFreeIndependence OAI.CliqueFreeIndependence.FiniteEntropy
open scoped BigOperators
open Finset
attribute [local instance] Classical.propDecidable
universe u v
variable {I : Type u} [Fintype I]
variable {J : Type v} [Fintype J]

theorem OAI.CliqueFreeIndependence.FiniteEntropy.entropy_supported_concentration (D s : Finset I) (hsD : s ⊆ D) {w p : I → ℝ}
    (hw : ∀ i ∈ D, 0 < w i) (hp : IsProb p) (hs : ∀ i, i ∉ D → p i = 0)
    {m M : ℝ} (hm : 1 ≤ m) (hM : 0 < M)
    (hwsmall : ∑ i ∈ s, w i ≤ m) (hwall : ∑ i ∈ D, w i ≤ M) :
    entropy w p ≤ Real.log 2 + Real.log m + (1 - ∑ i ∈ s, p i) * Real.log M := by sorry
