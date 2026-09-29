-- Prove2me | Theorems.Thm_NumberField_AdicCompletion_map_linearMap_eq_norm_det_inv_smul_of_isAddHaarMeasure
-- name    : NumberField.AdicCompletion.map_linearMap_eq_norm_det_inv_smul_of_isAddHaarMeasure
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:56.923973+00:00
-- url     : https://prove2.me/theorems/7f4ef765-7ead-5138-b8b9-fa0e75c791fb
-- title:
--   Haar measure under a linear map over Kᵥ
-- statement:
--   Let $K$ be a number field, $v$ a height-one prime of its ring of integers $\mathcal{O}_K$, and $F = K_v$ the associated adic completion. Let $V$ be an additive commutative group equipped with an $F$-module structure which is finite-dimensional over $F$, carrying a topology which is the $F$-module topology (so the topology induced from $F$ through any basis), together with a measurable structure which is the Borel structure of that topology. Let $\nu$ be a measure on $V$ that is an additive Haar measure, and let $T \colon V \to V$ be an $F$-linear endomorphism whose determinant $\det T \in F$ is nonzero. Then the pushforward of $\nu$ along $T$ equals the rescaling of $\nu$ by the extended-real scalar $\mathrm{ofReal}\,\|\det T\|^{-1}$, where $\|\cdot\|$ is the norm on the completion $F$: $$T_*\nu = |\det T|^{-1}\,\nu .$$ Equivalently, $\nu(T(B)) = |\det T|\,\nu(B)$ for Borel $B \subseteq V$.
--
--   This is the coordinate-free change-of-variables formula over a non-archimedean completion of a number field: the module of an invertible linear automorphism $T$ of the locally compact group $V$ is $|\det T|$. It is used in the local integration computations for automorphic forms, for instance with $V$ a finite commutative $F$-algebra $E$ and $T$ multiplication by a unit of $E$ (whose $F$-determinant is the norm), and with $V = E^n$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_AdicCompletion_map_linearMap_eq_norm_det_inv_smul_of_isAddHaarMeasure.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField IsDedekindDomain MeasureTheory

theorem NumberField.AdicCompletion.map_linearMap_eq_norm_det_inv_smul_of_isAddHaarMeasure
    (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))
    (V : Type) [AddCommGroup V] [Module (v.adicCompletion K) V]
    [FiniteDimensional (v.adicCompletion K) V]
    [TopologicalSpace V] [IsModuleTopology (v.adicCompletion K) V]
    [MeasurableSpace V] [BorelSpace V]
    (ν : Measure V) [ν.IsAddHaarMeasure]
    (T : V →ₗ[v.adicCompletion K] V) (hT : LinearMap.det T ≠ 0) :
    Measure.map T ν = ENNReal.ofReal ‖LinearMap.det T‖⁻¹ • ν := by sorry
