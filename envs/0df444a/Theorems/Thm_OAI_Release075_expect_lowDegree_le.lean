-- Prove2me | Theorems.Thm_OAI_Release075_expect_lowDegree_le
-- name    : OAI.Release075.expect_lowDegree_le
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T07:42:16.593238+00:00
-- url     : https://prove2.me/theorems/eb08d403-f5dd-4bda-b7e1-a82ab647d957
-- title:
--   Expected number of low-degree points
-- statement:
--   For marks $a\in V$ in a vector space over a field $K$ and a projective direction $d$ with chosen representative $\hat d$, the point $z$ is punctured-incident to the line $(a,d)$ when $z\ne a$ and $z=a+t\hat d$ for some $t\in K$. For marks $S$ in a finite space $V$ and a uniformly random direction assignment $\omega:S\to\mathbb P(V)$, the degree of $z$ counts marks to whose line $z$ is punctured-incident. Its mean is $\mu(z)=\sum_{a\in S}[z\ne a]/|\mathbb P(V)|$. If $\mu(z)\ge\mu>0$ for all $z$ and $2T\le\mu$, then
--   $$
--   \mathbb E_\omega\,\#\{z\in V:\ \deg_\omega(z)<T\}\le\frac{4|V|}{\mu}.
--   $$
--
--   Low-degree points are among the exceptional points of the construction, so this bounds their expected number.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/GroupTheory/Hyperbolic/Incidence.lean#L330-L360

import Mathlib
import Definitions.Def_TorsionFreeHyperbolic
import Definitions.Def_OAI_GroupTheory_Hyperbolic_MatrixRank
import Definitions.Def_OAI_GroupTheory_Hyperbolic_Incidence

open OAI OAI.Release075
open scoped BigOperators
attribute [local instance] Classical.propDecidable
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [Fintype (Projectivization K V)] [Nontrivial V]

theorem OAI.Release075.expect_lowDegree_le [Fintype V] (S : Finset V) (T : ℕ) (μ : ℝ)
    (hμ : 0 < μ) (hT : 2 * (T : ℝ) ≤ μ)
    (hlower : ∀ z : V, μ ≤ pointMean (K := K) S z) :
    (𝔼 ω : S → Projectivization K V,
      ((Finset.univ.filter (fun z : V => pointDegree S ω z < T)).card : ℝ)) ≤
        4 * (Fintype.card V : ℝ) / μ := by sorry
