-- Prove2me | Theorems.Thm_OAI_MatchingEntropy_entropy_maximizer_support
-- name    : OAI.MatchingEntropy.entropy_maximizer_support
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T00:58:58.417782+00:00
-- url     : https://prove2.me/theorems/33066945-9f48-4842-93b9-8fa4e6d0159d
-- title:
--   An entropy maximizer on a segment is positive wherever the other endpoint is
-- statement:
--   Let $I$ be a finite index set and $H(z)=\sum_{i\in I}-z_i\log z_i$ (with $0\log0=0$). Let $p,q\in\mathbb{R}^I$ have nonnegative coordinates, and suppose that $p$ has maximal entropy on the segment from $p$ to $q$:
--   $$
--   H\big((1-t)p+tq\big)\le H(p)\qquad\text{for all }t\in[0,1].
--   $$
--   Then for every $j\in I$ with $q_j>0$ we have $p_j>0$. In other words, $\{j: q_j>0\}\subseteq\{j: p_j>0\}$.
--
--   If $p$ maximizes $H$ over a convex set $K$ of nonnegative vectors, the hypothesis holds for every $q\in K$. Hence the support of any entropy maximizer on $K$ contains the support of every point of $K$. This is how positivity of an optimal law is obtained from optimality alone. The vectors need not be probability vectors.
--
--   **Formalization Note** Entropy is `entropy p = ∑ i, Real.negMulLog (p i)`, and the segment condition is quantified over `t ∈ Set.Icc 0 1`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/PerfectMatching/Optimizer.lean#L56-L77

import Mathlib
import Definitions.Def_MatchingEntropy
import Definitions.Def_OAI_Combinatorics_PerfectMatching_Model
import Definitions.Def_OAI_Combinatorics_PerfectMatching_Basic

open OAI OAI.MatchingEntropy
open scoped BigOperators Topology
open Filter
variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]

theorem OAI.MatchingEntropy.entropy_maximizer_support {ι : Type*} [Fintype ι] {p q : ι → ℝ}
    (hp : ∀ i, 0 ≤ p i) (hq : ∀ i, 0 ≤ q i)
    (hmax : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      entropy (fun i => (1-t)*p i+t*q i) ≤ entropy p) {j : ι} (hjq : 0 < q j) :
    0 < p j := by sorry
