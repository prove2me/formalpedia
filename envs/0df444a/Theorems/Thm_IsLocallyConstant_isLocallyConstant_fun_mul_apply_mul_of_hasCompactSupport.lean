-- Prove2me | Theorems.Thm_IsLocallyConstant_isLocallyConstant_fun_mul_apply_mul_of_hasCompactSupport
-- name    : IsLocallyConstant.isLocallyConstant_fun_mul_apply_mul_of_hasCompactSupport
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:59.02392+00:00
-- url     : https://prove2.me/theorems/559db1c3-82e9-5535-a344-3458a6061ba0
-- title:
--   Two-sided slice families of compactly supported locally constant functions
-- statement:
--   Let $G$ be a group carrying a topology making it a topological group, let $Y$ be a type equipped with a distinguished element $0$, and let $f : G \to Y$ be locally constant (every point has a neighbourhood on which $f$ is constant, equivalently every preimage under $f$ is open) and of compact support, meaning that the closure of $\{g : f(g) \neq 0\}$ is compact. Let $S$ be an arbitrary type and $n : S \to G$ an arbitrary map; no topology or structure on $S$ is assumed, and $n$ is subject to no condition. The assertion is that the map
--   $$G \times G \longrightarrow (S \to Y), \qquad (k, k') \longmapsto \bigl(s \mapsto f(k\, n(s)\, k')\bigr),$$
--   is locally constant on the product $G \times G$, the target being the bare function type $S \to Y$: every point $(k_0, k_0')$ has a neighbourhood on which the whole slice function $s \mapsto f(k\, n(s)\, k')$ coincides, as a function of $s$, with $s \mapsto f(k_0\, n(s)\, k_0')$.
--
--   This is the local-constancy input for the standard fact that a locally constant compactly supported function on a locally profinite group is bi-invariant under some compact open subgroup, so that its two-sided translates along an arbitrary family of group elements form a locally constant (hence, over a compact parameter set, finite) family. It is used in the uniform estimates for unipotent integrals and averages attached to automorphic test functions, namely in [`AutomorphicForm.exists_forall_norm_tsum_sub_inv_measure_mul_integral_comp_unipotentGL2_le_of_isCompact`](thm.html#AutomorphicForm.exists_forall_norm_tsum_sub_inv_measure_mul_integral_comp_unipotentGL2_le_of_isCompact) and [`AutomorphicForm.norm_tsum_sub_average_le_mul_inv_archHeight_pow_of_isFactorizableTestFn`](thm.html#AutomorphicForm.norm_tsum_sub_average_le_mul_inv_archHeight_pow_of_isFactorizableTestFn).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_IsLocallyConstant_isLocallyConstant_fun_mul_apply_mul_of_hasCompactSupport.lean

import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.Topology.LocallyConstant.Basic

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem IsLocallyConstant.isLocallyConstant_fun_mul_apply_mul_of_hasCompactSupport
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] {Y : Type*} [Zero Y]
    {f : G → Y} (hf : IsLocallyConstant f) (hsupp : HasCompactSupport f) {S : Type*} (n : S → G) :
    IsLocallyConstant (fun kk : G × G => fun s => f (kk.1 * n s * kk.2)) := by sorry
