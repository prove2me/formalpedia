-- Prove2me | Theorems.Thm_OAI_Release075_CycleCandidate_expect_occurs
-- name    : OAI.Release075.CycleCandidate.expect_occurs
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T07:41:16.472069+00:00
-- url     : https://prove2.me/theorems/32eaa172-30e3-4cd6-b60b-605fb38f2c5d
-- title:
--   Probability that a cycle candidate occurs
-- statement:
--   Fix a finite set $S\subseteq V$ of marks in a finite vector space $V$ over a finite field $K$, a random direction assignment $\omega:S\to\mathbb P(V)$, and a map $\sigma:A\to A$. A cycle candidate is a pair $(p,t)$ with $p:A\to V$ injective, $p(\sigma a)\ne p(a)$, and attempted marks $m_a=p(a)+t_a(p(\sigma a)-p(a))$ that are distinct elements of $S$. It occurs for $\omega$ when $\omega(m_a)$ is the direction of $p(\sigma a)-p(a)$ for every $a$. Over a uniformly random direction assignment $\omega$, each candidate $c$ occurs with probability
--   $$
--   \mathbb E_\omega\,[c\text{ occurs}]=\Bigl(\frac1{|\mathbb P(V)|}\Bigr)^{|A|}.
--   $$
--
--   The distinctness of the attempted marks is what makes the directions independent.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/GroupTheory/Hyperbolic/Incidence.lean#L220-L243

import Mathlib
import Definitions.Def_TorsionFreeHyperbolic
import Definitions.Def_OAI_GroupTheory_Hyperbolic_MatrixRank
import Definitions.Def_OAI_GroupTheory_Hyperbolic_Incidence

open OAI OAI.Release075 OAI.Release075.CycleCandidate
open scoped BigOperators
attribute [local instance] Classical.propDecidable
variable {A K V : Type*} [Field K] [AddCommGroup V] [Module K V]
variable {S : Finset V} {σ : A → A}

theorem OAI.Release075.CycleCandidate.expect_occurs [Fintype A] [Fintype (Projectivization K V)] [Nontrivial V]
    (c : CycleCandidate (K := K) S σ) :
    (𝔼 ω : S → Projectivization K V, if c.Occurs ω then (1 : ℝ) else 0) =
      (1 / Fintype.card (Projectivization K V) : ℝ) ^ Fintype.card A := by sorry
