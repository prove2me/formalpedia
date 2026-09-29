-- Prove2me | Theorems.Thm_MeasureTheory_exists_nhds_one_forall_eLpNorm_comp_mul_sub_lt_of_memLp_two
-- name    : MeasureTheory.exists_nhds_one_forall_eLpNorm_comp_mul_sub_lt_of_memLp_two
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:12.429051+00:00
-- url     : https://prove2.me/theorems/151d1c34-2f26-5939-8e55-3baf7a278762
-- title:
--   Strong continuity at 1 of right translation on L²(G,μ)
-- statement:
--   Let $G$ be a group carrying a topology making it a topological group, assumed locally compact, Hausdorff and second countable, and equipped with a measurable space structure which is the Borel structure of its topology. Let $\mu$ be a measure on $G$ that is a Haar measure (in particular left invariant) and is in addition right invariant. Let $F : G \to \mathbb{C}$ be a function belonging to $L^2(\mu)$ in the sense that `MemLp F 2 μ` holds, and let $\varepsilon$ be a real number with $\varepsilon > 0$. The conclusion asserts the existence of a set $V$ in the neighbourhood filter of the identity $1 \in G$ such that for every $x \in V$ one has
--   $$\operatorname{eLpNorm}\bigl(g \mapsto F(gx) - F(g),\, 2,\, \mu\bigr) < \mathrm{ofReal}\,\varepsilon$$
--   in $[0,\infty]$, i.e. the $L^2(\mu)$-norm of the difference between $F$ translated on the right by $x$ and $F$ itself is strictly smaller than $\varepsilon$. Note that $V$ is only asserted to be a neighbourhood of $1$, not an open set.
--
--   This is the continuity at the identity of the right regular representation of $G$ on $L^2(G,\mu)$, for a Haar measure that is also right invariant. It is the abstract ingredient behind the strong continuity of right translation used in the adelic setting, where it is applied on $GL_2(\mathbb{A}_K)$ to the characteristic function of a truncation domain and to its product with a given $L^2$ function, by [`AutomorphicForm.exists_nhds_one_forall_eLpNorm_comp_mul_sub_lt_of_isAutomorphicFnAt_canonicalTruncationDomain`](thm.html#AutomorphicForm.exists_nhds_one_forall_eLpNorm_comp_mul_sub_lt_of_isAutomorphicFnAt_canonicalTruncationDomain).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_MeasureTheory_exists_nhds_one_forall_eLpNorm_comp_mul_sub_lt_of_memLp_two.lean

import Definitions.Def_NumberField_AdelicHaar

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory Topology
open scoped ENNReal

theorem MeasureTheory.exists_nhds_one_forall_eLpNorm_comp_mul_sub_lt_of_memLp_two
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G]
    [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
    (μ : Measure G) [μ.IsHaarMeasure] [μ.IsMulRightInvariant]
    (F : G → ℂ) (hF : MemLp F 2 μ) (ε : ℝ) (hε : 0 < ε) :
    ∃ V ∈ 𝓝 (1 : G), ∀ x ∈ V, eLpNorm (fun g => F (g * x) - F g) 2 μ < ENNReal.ofReal ε := by sorry
