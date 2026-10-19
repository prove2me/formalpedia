-- Prove2me | Theorems.Thm_OAI_Release075_cycleCandidate_of_incidence
-- name    : OAI.Release075.cycleCandidate_of_incidence
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T07:44:18.843081+00:00
-- url     : https://prove2.me/theorems/21227fc9-bb30-409b-b7d0-ecb46eaf5678
-- title:
--   Incidence cycles are counted among the cycle candidates
-- statement:
--   Fix a finite set $S\subseteq V$ of marks in a finite vector space $V$ over a finite field $K$, a random direction assignment $\omega:S\to\mathbb P(V)$, and a map $\sigma:A\to A$. A cycle candidate is a pair $(p,t)$ with $p:A\to V$ injective, $p(\sigma a)\ne p(a)$, and attempted marks $m_a=p(a)+t_a(p(\sigma a)-p(a))$ that are distinct elements of $S$. It occurs for $\omega$ when $\omega(m_a)$ is the direction of $p(\sigma a)-p(a)$ for every $a$. Let $s\ge2$, let $p:\mathbb Z/s\to V$ be injective points and $l:\mathbb Z/s\to S$ injective marks such that both $p_i$ and $p_{i+1}$ are punctured-incident to the line $(l_i,\omega(l_i))$ for each $i$. Then there is a cycle candidate $c$ for the cyclic shift of $\mathbb Z/s$ with
--   $$
--   c\text{ occurs for }\omega\quad\text{and}\quad m_i=l_i\ \ (i\in\mathbb Z/s).
--   $$
--
--   Thus the expected count of occurring candidates also bounds the number of short incidence cycles.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/GroupTheory/Hyperbolic/Incidence.lean#L503-L525

import Mathlib
import Definitions.Def_TorsionFreeHyperbolic
import Definitions.Def_OAI_GroupTheory_Hyperbolic_MatrixRank
import Definitions.Def_OAI_GroupTheory_Hyperbolic_Incidence

open OAI OAI.Release075
open scoped BigOperators
attribute [local instance] Classical.propDecidable
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

theorem OAI.Release075.cycleCandidate_of_incidence {S : Finset V} (ω : S → Projectivization K V)
    {s : ℕ} (hs : 2 ≤ s) (p : Fin s → V) (l : Fin s → S)
    (hp : Function.Injective p) (hl : Function.Injective l)
    (h : ∀ i, PuncturedIncidence (l i).val (p i) (ω (l i)) ∧
      PuncturedIncidence (l i).val (p (finRotate s i)) (ω (l i))) :
    ∃ c : CycleCandidate (K := K) S (finRotate s), c.Occurs ω ∧ ∀ i, c.marks i = l i := by sorry
