-- Prove2me | Theorems.Thm_NumberField_InfiniteAdeleRing_map_linearMap_eq_inv_prod_norm_archEval_det_pow_mult_smul_of_isAddHaarMeasure
-- name    : NumberField.InfiniteAdeleRing.map_linearMap_eq_inv_prod_norm_archEval_det_pow_mult_smul_of_isAddHaarMeasure
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:56.923973+00:00
-- url     : https://prove2.me/theorems/c4b6a490-a8ca-590e-8538-4cede4d02cb9
-- title:
--   Module of a K_∞-linear automorphism of a finite free module
-- statement:
--   Let $K$ be a number field and let $V$ be an additive commutative group carrying a module structure over the infinite adele ring $K_\infty =$ `InfiniteAdeleRing K` (the product of the completions $K_w$ over the infinite places $w$ of $K$) which is finite and free as a $K_\infty$-module, equipped with a topology that is the $K_\infty$-module topology and with a measurable structure which is the Borel structure of that topology. Let $\nu$ be an additive Haar measure on $V$, and let $T \colon V \to V$ be a $K_\infty$-linear endomorphism whose determinant $\det T \in K_\infty$ is a unit. Then the pushforward measure $T_*\nu$ equals the scalar multiple of $\nu$ by the extended nonnegative real number obtained from the real number $$\Big(\prod_{w \mid \infty} \big\|\,\mathrm{archEval}_{K,w}(\det T)\,\big\|^{\,w.\mathrm{mult}}\Big)^{-1},$$ where the product runs over the infinite places $w$ of $K$, $\mathrm{archEval}_{K,w}$ is the ring homomorphism $K_\infty \to K_w$ evaluating an element at the place $w$, $\|\cdot\|$ is the norm of the completion $K_w$, and $w.\mathrm{mult}$ is $1$ at a real place and $2$ at a complex place.
--
--   This computes the module (the scaling factor of additive Haar measure) of a $K_\infty$-linear automorphism of a finite free module over the archimedean part of the adeles, the archimedean counterpart of the local statement $T_*\nu = |\det T|_v^{-1}\nu$ at a finite place. It is used in the measure-theoretic estimates for automorphic forms, being cited in the computation of the Haar measure of translates and dilates in tensor constructions over $K_\infty$ and in the corresponding change-of-variables identity for integrals.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_InfiniteAdeleRing_map_linearMap_eq_inv_prod_norm_archEval_det_pow_mult_smul_of_isAddHaarMeasure.lean

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_NumberField_AdelicLevel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel IsDedekindDomain
open scoped TensorProduct TensorProduct.RightActions

open scoped Classical in

theorem NumberField.InfiniteAdeleRing.map_linearMap_eq_inv_prod_norm_archEval_det_pow_mult_smul_of_isAddHaarMeasure
    (K : Type) [Field K] [NumberField K]
    (V : Type) [AddCommGroup V] [Module (InfiniteAdeleRing K) V]
    [Module.Finite (InfiniteAdeleRing K) V] [Module.Free (InfiniteAdeleRing K) V]
    [TopologicalSpace V] [IsModuleTopology (InfiniteAdeleRing K) V]
    [MeasurableSpace V] [BorelSpace V]
    (ν : Measure V) [ν.IsAddHaarMeasure]
    (T : V →ₗ[InfiniteAdeleRing K] V) (hT : IsUnit (LinearMap.det T)) :
    Measure.map T ν =
      ENNReal.ofReal ((∏ w : NumberField.InfinitePlace K,
        ‖NumberField.AdelicLevel.archEval K w (LinearMap.det T)‖ ^ w.mult)⁻¹) • ν := by sorry
