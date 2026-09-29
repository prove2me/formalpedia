-- Prove2me | Theorems.Thm_NumberField_AdicCompletion_map_matrix_mulVec_pi_eq_smul_pi
-- name    : NumberField.AdicCompletion.map_matrix_mulVec_pi_eq_smul_pi
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:56.923973+00:00
-- url     : https://prove2.me/theorems/b7ce8fa6-d00a-57bc-9071-dc1660e07c4c
-- title:
--   Haar measure on Kᵥ^ι scales by |det M|
-- statement:
--   Let $K$ be a number field, $v$ a nonzero prime ideal of its ring of integers $\mathcal{O}_K$, and let $K_v$ denote the $v$-adic completion of $K$, equipped with a measurable space structure that is the Borel structure of its topology. Let $\mu$ be a measure on $K_v$ that is an additive Haar measure, let $\iota$ be a finite type, and let $M$ be an $\iota\times\iota$ matrix over $K_v$ with $\det M \neq 0$. Then the pushforward of the product measure $\bigotimes_{i\in\iota}\mu$ on $\iota \to K_v$ along the linear map $x \mapsto Mx$ (matrix–vector multiplication) equals the scalar multiple of that same product measure by the extended nonnegative real $\mathrm{ofReal}\,\|\det M\|^{-1}$, where $\|\cdot\|$ is the norm of $K_v$. Equivalently, the measure of a preimage under $x \mapsto Mx$ is $\|\det M\|^{-1}$ times the measure of the set; no finiteness, regularity or normalisation of $\mu$ beyond being an additive Haar measure is assumed.
--
--   This is the linear change-of-variables formula over a nonarchimedean local field: the module of the automorphism $x \mapsto Mx$ of $K_v^{\iota}$ is the normalised absolute value $|\det M|$. It is used in the local harmonic analysis over $K_v$, for instance in computing integrals over local centralisers and tori in coordinates and in the Fourier-theoretic computations attached to cubic induction.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_AdicCompletion_map_matrix_mulVec_pi_eq_smul_pi.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField IsDedekindDomain MeasureTheory

theorem NumberField.AdicCompletion.map_matrix_mulVec_pi_eq_smul_pi
    (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))
    [MeasurableSpace (v.adicCompletion K)] [BorelSpace (v.adicCompletion K)]
    (μ : Measure (v.adicCompletion K)) [μ.IsAddHaarMeasure]
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι (v.adicCompletion K)) (hM : M.det ≠ 0) :
    Measure.map (fun x : ι → v.adicCompletion K => M.mulVec x) (Measure.pi fun _ : ι => μ) =
      ENNReal.ofReal ‖M.det‖⁻¹ • Measure.pi fun _ : ι => μ := by sorry
