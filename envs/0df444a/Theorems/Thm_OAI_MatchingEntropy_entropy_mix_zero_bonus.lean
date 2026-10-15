-- Prove2me | Theorems.Thm_OAI_MatchingEntropy_entropy_mix_zero_bonus
-- name    : OAI.MatchingEntropy.entropy_mix_zero_bonus
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T00:58:38.517636+00:00
-- url     : https://prove2.me/theorems/b1e12c8f-dd1e-4092-9dde-e7f72ef0543b
-- title:
--   Mixing mass into a zero coordinate gains the entropy bonus $q_j\,\eta(t)$ beyond concavity
-- statement:
--   Let $I$ be a finite index set. Write $\eta(s)=-s\log s$ (with $\eta(0)=0$) and $H(z)=\sum_{i\in I}\eta(z_i)$ for $z\in\mathbb{R}^I$. Let $p,q\in\mathbb{R}^I$ have nonnegative coordinates, let $j\in I$ be an index with $p_j=0$, and let $t\in[0,1]$. Then
--   $$
--   (1-t)\,H(p)+t\,H(q)+q_j\,\eta(t)\;\le\;H\big((1-t)p+tq\big),
--   \qquad\text{where }\eta(t)=-t\log t .
--   $$
--
--   Concavity of entropy alone gives this inequality without the term $q_j\eta(t)$. The extra term is of order $t\log(1/t)$ as $t\to0^+$, so it dominates any loss that is linear in $t$. This is the boundary argument showing that moving from a vector with a zero coordinate towards a vector that charges that coordinate increases the entropy at an infinite initial rate. It is the key input for proving that entropy maximizers over convex sets have maximal support. The vectors $p$ and $q$ need not be probability vectors.
--
--   **Formalization Note** Entropy is `entropy p = ∑ i, Real.negMulLog (p i)`, and the bonus term is `q j * Real.negMulLog t`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/PerfectMatching/Optimizer.lean#L31-L54

import Mathlib
import Definitions.Def_MatchingEntropy
import Definitions.Def_OAI_Combinatorics_PerfectMatching_Model
import Definitions.Def_OAI_Combinatorics_PerfectMatching_Basic

open OAI OAI.MatchingEntropy
open scoped BigOperators Topology
open Filter
variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]

theorem OAI.MatchingEntropy.entropy_mix_zero_bonus {ι : Type*} [Fintype ι] {p q : ι → ℝ}
    (hp : ∀ i, 0 ≤ p i) (hq : ∀ i, 0 ≤ q i) {j : ι} (hj : p j = 0)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    (1-t) * entropy p + t * entropy q + q j * Real.negMulLog t ≤
      entropy (fun i => (1-t)*p i + t*q i) := by sorry
