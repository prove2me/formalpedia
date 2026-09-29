-- Prove2me | Theorems.Thm_MeasureTheory_Measure_measure_coe_eq_relIndex_mul_of_le_of_isAddLeftInvariant
-- name    : MeasureTheory.Measure.measure_coe_eq_relIndex_mul_of_le_of_isAddLeftInvariant
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:12.429051+00:00
-- url     : https://prove2.me/theorems/e2543683-2d7a-5aee-8b3d-ceaf3c2acb6a
-- title:
--   Relative index scaling for a left-invariant measure
-- statement:
--   Let $G$ be an additive group equipped with a measurable space structure for which addition is measurable, and let $\mu$ be a measure on $G$ that is invariant under left translations. Let $H \le H'$ be additive subgroups of $G$, assume the underlying set of $H$ is measurable, and assume the relative index `H.relIndex H'`, i.e. the number of cosets of $H \cap H'$ in $H'$ (the index of $H$ viewed inside $H'$), is non-zero, so that it is a genuine finite cardinality. Then the measure of the underlying set of $H'$ equals the product of this relative index, coerced into $[0,\infty]$, with the measure of the underlying set of $H$:
--   $$\mu(H') = [H' : H]\cdot\mu(H).$$
--   Note that the measurability hypothesis is imposed only on $H$; measurability of $H'$ is not assumed, and no $\sigma$-finiteness or Haar-type regularity is required, the measure being merely left-invariant.
--
--   This is the elementary coset-counting index formula for an invariant measure, in its additive form. It is used in the lattice bookkeeping for covolume and integral identities in the automorphic-forms part of the development, for instance in [`AutomorphicForm.setLIntegral_lattice_norm_det_mul_relIndex_eq_setLIntegral_closure_conj_mul_relIndex`](thm.html#AutomorphicForm.setLIntegral_lattice_norm_det_mul_relIndex_eq_setLIntegral_closure_conj_mul_relIndex) and in the computations comparing norms and measures of commensurable lattices.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_MeasureTheory_Measure_measure_coe_eq_relIndex_mul_of_le_of_isAddLeftInvariant.lean

import Mathlib.MeasureTheory.Group.Measure
import Mathlib.GroupTheory.Index

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory

theorem MeasureTheory.Measure.measure_coe_eq_relIndex_mul_of_le_of_isAddLeftInvariant
    {G : Type*} [AddGroup G] [MeasurableSpace G] [MeasurableAdd G] (μ : Measure G) [μ.IsAddLeftInvariant]
    (H H' : AddSubgroup G) (hle : H ≤ H') (hH : MeasurableSet (H : Set G)) (hfin : H.relIndex H' ≠ 0) :
    μ (H' : Set G) = (H.relIndex H' : ENNReal) * μ (H : Set G) := by sorry
