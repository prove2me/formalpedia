-- Prove2me | Theorems.Thm_OAI_MatchingEntropy_entropy_partition_bound
-- name    : OAI.MatchingEntropy.entropy_partition_bound
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T01:02:40.113262+00:00
-- url     : https://prove2.me/theorems/b7e2f409-1656-4fc9-8fc4-e65e7c93090b
-- title:
--   Gibbs variational inequality for a finite exponential tilt
-- statement:
--   Let $\iota$ be a finite set and let $p$ and $q$ be probability vectors on $\iota$ (nonnegative entries summing to $1$) such that $q$ is supported in the support of $p$: $q_i=0$ whenever $p_i=0$. For a function $a:\iota\to\mathbb R$ and a real parameter $t$, let
--
--   $$
--   Z_p(a,t)=\sum_{i\in\iota}p_i\,e^{t a_i}
--   $$
--
--   be the exponential partition function of $a$ under $p$, and let $H(q)=-\sum_i q_i\log q_i$ (with $0\log0=0$) be the Shannon entropy of $q$. Then
--
--   $$
--   H(q)\;\le\;\log Z_p(a,t)\;-\;\sum_{i\in\iota}q_i\log p_i\;-\;t\sum_{i\in\iota}q_i\,a_i .
--   $$
--
--   This is Gibbs' variational inequality for the exponentially tilted law $p_i e^{ta_i}/Z_p(a,t)$. It bounds the entropy of every law carried by the support of $p$, including laws that vanish on part of that support, by an expression that is affine in $q$ and involves the reference law $p$ only through $\log p_i$ and the partition function. It is the basic tool for turning a single reference law into upper bounds on maximum entropies.
--
--   **Formalization Note** Terms with $p_i=0$ cause no trouble: there $q_i=0$, and in Lean also $\log 0=0$, so $q_i\log p_i=0$. The entropy is `entropy q`, the sum of `Real.negMulLog (q i)`, and $Z_p(a,t)$ is `partition p a t`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/PerfectMatching/Duality.lean#L44-L73

import Mathlib
import Definitions.Def_MatchingEntropy
import Definitions.Def_OAI_Combinatorics_PerfectMatching_Model
import Definitions.Def_OAI_Combinatorics_PerfectMatching_Basic
import Definitions.Def_OAI_Combinatorics_PerfectMatching_Duality

open OAI OAI.MatchingEntropy
open scoped BigOperators Topology
open Filter
variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]

theorem OAI.MatchingEntropy.entropy_partition_bound {ι : Type*} [Fintype ι] {p q : ι → ℝ}
    (hp : p ∈ probabilitySimplex ι) (hq : q ∈ probabilitySimplex ι)
    (hsupp : ∀ i, p i = 0 → q i = 0) (a : ι → ℝ) (t : ℝ) :
    entropy q ≤ Real.log (partition p a t) - ∑ i, q i*Real.log (p i) -
      t * ∑ i, q i*a i := by sorry
