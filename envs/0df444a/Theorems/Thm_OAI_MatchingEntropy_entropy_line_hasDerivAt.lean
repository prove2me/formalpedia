-- Prove2me | Theorems.Thm_OAI_MatchingEntropy_entropy_line_hasDerivAt
-- name    : OAI.MatchingEntropy.entropy_line_hasDerivAt
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T01:00:30.338001+00:00
-- url     : https://prove2.me/theorems/4890d3d7-1b63-4a76-b4fb-062678de6bf9
-- title:
--   Derivative of entropy at $t=0$ along a line that does not leave the support
-- statement:
--   Let $I$ be a finite index set, write $\eta(s)=-s\log s$ and $H(z)=\sum_{i\in I}\eta(z_i)$ for $z\in\mathbb{R}^I$. Let $p,v\in\mathbb{R}^I$ be arbitrary real vectors such that $v_i=0$ whenever $p_i=0$. Then the function $t\mapsto H(p+tv)$ is differentiable at $t=0$, with
--   $$
--   \frac{d}{dt}\Big|_{t=0}H(p+tv)=-\sum_{i\in I}v_i\log p_i-\sum_{i\in I}v_i .
--   $$
--
--   This is the first-order expansion of entropy in a direction that does not move the zero coordinates. Coordinates with $p_i=0$ contribute nothing to either side. For directions with $\sum_i v_i=0$, such as differences of probability vectors, the derivative reduces to $-\sum_i v_i\log p_i$. It is the basis of the first-order optimality conditions for maximum-entropy laws.
--
--   **Formalization Note** No sign condition on $p$ is assumed. Lean's real logarithm satisfies $\log 0=0$ and $\log s=\log|s|$ for $s<0$, so $\eta(s)=-s\log|s|$ for negative $s$. This function is differentiable at every $s\neq0$ with derivative $-\log s-1$, which is why the formula holds for all real $p$ obeying the support condition. Differentiability is expressed with `HasDerivAt`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/PerfectMatching/Optimizer.lean#L131-L151

import Mathlib
import Definitions.Def_MatchingEntropy
import Definitions.Def_OAI_Combinatorics_PerfectMatching_Model
import Definitions.Def_OAI_Combinatorics_PerfectMatching_Basic

open OAI OAI.MatchingEntropy
open scoped BigOperators Topology
open Filter
variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]

theorem OAI.MatchingEntropy.entropy_line_hasDerivAt {ι : Type*} [Fintype ι] (p v : ι → ℝ)
    (hsupp : ∀ i, p i = 0 → v i = 0) :
    HasDerivAt (fun t : ℝ => entropy (fun i => p i+t*v i))
      (-∑ i, v i * Real.log (p i) - ∑ i, v i) 0 := by sorry
