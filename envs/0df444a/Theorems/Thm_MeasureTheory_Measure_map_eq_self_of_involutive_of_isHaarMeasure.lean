-- Prove2me | Theorems.Thm_MeasureTheory_Measure_map_eq_self_of_involutive_of_isHaarMeasure
-- name    : MeasureTheory.Measure.map_eq_self_of_involutive_of_isHaarMeasure
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:12.429051+00:00
-- url     : https://prove2.me/theorems/9a3003e3-0bd7-54cb-a926-a78624a14b62
-- title:
--   Continuous involutive automorphisms preserve Haar measure
-- statement:
--   Let $G$ be a group carrying a topology making it a topological group, assumed locally compact and second countable, and equipped with a measurable space structure which is the Borel structure of the topology. Let $\mu$ be a measure on $G$ which is a (left) Haar measure, i.e. left invariant, finite on compact sets and positive on nonempty open sets. Let $\theta : G \simeq^* G$ be a group automorphism of $G$ (a multiplicative equivalence, so bijective and multiplicative with its inverse), assume that the underlying map of $\theta$ is continuous, and assume that $\theta$ is involutive in the sense that $\theta(\theta(g)) = g$ for every $g \in G$. Then the pushforward of $\mu$ along $\theta$ equals $\mu$, i.e. $\theta_*\mu = \mu$, in other words $\mu(\theta^{-1}(A)) = \mu(A)$ for all Borel sets $A$. Note that $\theta$ is assumed only to be a continuous abstract automorphism; continuity of the inverse is not hypothesised, being a consequence of the involutivity.
--
--   This is the statement that the modulus of a continuous involutive automorphism of a locally compact group is $1$, so that such an automorphism preserves every Haar measure. It is applied to the transpose-inverse involution on $\mathrm{GL}_2$ over a local field in the integral manipulations behind the lemmas [`AutomorphicForm.rate_eq_mul_rate_mul_measure_pow_three_of_forall_lintegral_mul_apply_col_det_eq_mul_lintegral_of_forall_isFundamentalDomain_op_inter_ideleNorm_det_Icc`](thm.html#AutomorphicForm.rate_eq_mul_rate_mul_measure_pow_three_of_forall_lintegral_mul_apply_col_det_eq_mul_lintegral_of_forall_isFundamentalDomain_op_inter_ideleNorm_det_Icc) and [`AutomorphicForm.setLIntegral_mul_ideleNorm_det_rpow_add_eq_setLIntegral_reflectPair_add_lintegral_mul_rate_of_isFundamentalDomain_twistedCentralizer_of_forall_ne_scalar_of_finrank_eq_two`](thm.html#AutomorphicForm.setLIntegral_mul_ideleNorm_det_rpow_add_eq_setLIntegral_reflectPair_add_lintegral_mul_rate_of_isFundamentalDomain_twistedCentralizer_of_forall_ne_scalar_of_finrank_eq_two).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_MeasureTheory_Measure_map_eq_self_of_involutive_of_isHaarMeasure.lean

import Mathlib.MeasureTheory.Measure.Haar.Basic

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open MeasureTheory

theorem MeasureTheory.Measure.map_eq_self_of_involutive_of_isHaarMeasure
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
    [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
    (μ : Measure G) [μ.IsHaarMeasure]
    (θ : G ≃* G) (hθ : Continuous θ) (hθinv : ∀ g : G, θ (θ g) = g) :
    Measure.map θ μ = μ := by sorry
