-- Prove2me | Theorems.Thm_OAI_CliqueFreeIndependence_FiniteEntropy_entropy_mix_gap
-- name    : OAI.CliqueFreeIndependence.FiniteEntropy.entropy_mix_gap
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T21:26:09.418802+00:00
-- url     : https://prove2.me/theorems/4c6daa5b-6ee3-426f-8fd8-60df01f3acb3
-- title:
--   Entropy of a mixture minus average entropy equals average divergence from the mixture
-- statement:
--   Let $I$ and $J$ be finite index sets. For vectors indexed by $I$ define the weighted entropy $H_w(p)=\sum_{i\in I}p_i\log\frac{w_i}{p_i}$ and the relative entropy (Kullback–Leibler divergence) $D(p\,\|\,q)=\sum_{i\in I}p_i\log\frac{p_i}{q_i}$, with the convention that terms with $p_i=0$ vanish; $\log$ is the natural logarithm. A probability vector has nonnegative entries summing to $1$.
--
--   Let $w_i>0$ for all $i\in I$, let $a=(a_j)_{j\in J}$ be a probability vector on $J$, and for each $j\in J$ let $p_j=(p_{j,i})_{i\in I}$ be a probability vector on $I$. Form the mixture $\bar p_i=\sum_{j\in J}a_j\,p_{j,i}$. Then
--
--   $$
--   H_w(\bar p)-\sum_{j\in J}a_j\,H_w(p_j)=\sum_{j\in J}a_j\,D\bigl(p_j\,\|\,\bar p\bigr).
--   $$
--
--   The left side is the entropy gained by mixing; the identity identifies it with the average divergence of the components from the mixture (the mutual information between the mixing index and the outcome). Since divergences of probability vectors are nonnegative, it quantifies the concavity of $H_w$, and it is used to control the entropy increase produced by averaging distributions, for instance under one step of a finite Markov kernel.
--
--   **Formalization Note** The functions are `entropy w p` and `divergence p q`, defined for arbitrary real vectors. In the statement every $j$ with $a_j>0$ has the support of $p_j$ inside the support of $\bar p$, so all logarithms that matter are of positive numbers; terms with $a_j=0$ vanish on both sides.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/CliqueFree/FiniteEntropy.lean#L192-L213

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

theorem OAI.CliqueFreeIndependence.FiniteEntropy.entropy_mix_gap {w : I → ℝ} (hw : ∀ i, 0 < w i)
    {a : J → ℝ} {p : J → I → ℝ} (ha : IsProb a) (hp : ∀ j, IsProb (p j)) :
    entropy w (fun i ↦ ∑ j, a j * p j i) - ∑ j, a j * entropy w (p j) =
      ∑ j, a j * divergence (p j) (fun i ↦ ∑ k, a k * p k i) := by sorry
