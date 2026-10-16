-- Prove2me | Theorems.Thm_OAI_CliqueFreeIndependence_FiniteEntropy_entropy_ge_neg_log_of_density
-- name    : OAI.CliqueFreeIndependence.FiniteEntropy.entropy_ge_neg_log_of_density
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T21:25:05.856443+00:00
-- url     : https://prove2.me/theorems/bbbbf4be-6200-4b8d-b05e-9a485fab63fc
-- title:
--   A density bound $p\le b\,w$ forces weighted entropy at least $-\log b$
-- statement:
--   For a finite index set $I$, a weight vector $w=(w_i)_{i\in I}$ and a vector $p=(p_i)_{i\in I}$, the weighted entropy is
--   $H_w(p)=\sum_{i\in I}p_i\log\frac{w_i}{p_i}$, with the convention that terms with $p_i=0$ vanish ($\log$ is the natural logarithm). A probability vector is a vector with $p_i\ge0$ for all $i$ and $\sum_ip_i=1$. For $w\equiv1$, $H_w(p)$ is the Shannon entropy of $p$, and in general $H_w(p)=H(p)+\sum_ip_i\log w_i$.
--
--   Let $w_i>0$ for all $i\in I$, let $p$ be a probability vector on $I$, and let $b>0$ be a real number such that $p_i\le b\,w_i$ for every $i$. Then
--
--   $$
--   H_w(p)=\sum_{i\in I}p_i\log\frac{w_i}{p_i}\ge-\log b .
--   $$
--
--   In words: if the density of $p$ with respect to the reference weights $w$ is bounded by $b$, then the weighted entropy of $p$ is at least $\log(1/b)$. For $w\equiv1$ this is the familiar fact that a distribution all of whose probabilities are at most $b$ has Shannon entropy at least $\log(1/b)$. It provides entropy lower bounds for random-walk laws whose density with respect to the vertex weights is controlled.
--
--   **Formalization Note** The weighted entropy is `entropy w p = ∑ i, p i * Real.log (w i / p i)`, where terms with $p_i=0$ vanish because $0\cdot x=0$. The hypothesis $w_i>0$ is part of the statement but is not used in the proof (it is in fact implied on the support of $p$ by $0<p_i\le bw_i$).
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/CliqueFree/FiniteEntropy.lean#L132-L146

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

theorem OAI.CliqueFreeIndependence.FiniteEntropy.entropy_ge_neg_log_of_density {w p : I → ℝ} (_hw : ∀ i, 0 < w i)
    (hp : IsProb p) {b : ℝ} (hb : 0 < b) (hden : ∀ i, p i ≤ b * w i) :
    -Real.log b ≤ entropy w p := by sorry
