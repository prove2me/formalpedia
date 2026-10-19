-- Prove2me | Theorems.Thm_OAI_Release075_expect_badCycles_le
-- name    : OAI.Release075.expect_badCycles_le
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T07:41:45.746879+00:00
-- url     : https://prove2.me/theorems/2670ac12-3c5d-41d6-8232-022b2399d266
-- title:
--   Expected number of occurring short-cycle candidates
-- statement:
--   Fix a finite set $S\subseteq V$ of marks in a finite vector space $V$ over a finite field $K$, a random direction assignment $\omega:S\to\mathbb P(V)$, and a map $\sigma:A\to A$. A cycle candidate is a pair $(p,t)$ with $p:A\to V$ injective, $p(\sigma a)\ne p(a)$, and attempted marks $m_a=p(a)+t_a(p(\sigma a)-p(a))$ that are distinct elements of $S$. It occurs for $\omega$ when $\omega(m_a)$ is the direction of $p(\sigma a)-p(a)$ for every $a$. Over a uniformly random $\omega$, the expected number of occurring candidates satisfies
--   $$
--   \mathbb E_\omega\,\#\{c:\ c\text{ occurs}\}\le|V|^{|A|}\,|K|^{|A|}\Bigl(\frac1{|\mathbb P(V)|}\Bigr)^{|A|}.
--   $$
--
--   It is used with $A=\{0,\dots,s-1\}$ and the cyclic shift for $2\le s\le6$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/GroupTheory/Hyperbolic/Incidence.lean#L251-L274

import Mathlib
import Definitions.Def_TorsionFreeHyperbolic
import Definitions.Def_OAI_GroupTheory_Hyperbolic_MatrixRank
import Definitions.Def_OAI_GroupTheory_Hyperbolic_Incidence

open OAI OAI.Release075
open scoped BigOperators
attribute [local instance] Classical.propDecidable
variable {A K V : Type*} [Field K] [AddCommGroup V] [Module K V]

theorem OAI.Release075.expect_badCycles_le [Fintype A] [Fintype K] [Fintype V]
    [Fintype (Projectivization K V)] [Nontrivial V]
    (S : Finset V) (σ : A → A) :
    (𝔼 ω : S → Projectivization K V, ((badCycles S σ ω).card : ℝ)) ≤
      (Fintype.card V : ℝ)^Fintype.card A * (Fintype.card K : ℝ)^Fintype.card A *
        (1 / Fintype.card (Projectivization K V) : ℝ)^Fintype.card A := by sorry
