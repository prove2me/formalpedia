-- Prove2me | Theorems.Thm_OAI_FourierBridge_fourier_seminorm_from_derivative_integrals
-- name    : OAI.FourierBridge.fourier_seminorm_from_derivative_integrals
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T22:14:48.204609+00:00
-- url     : https://prove2.me/theorems/4ab8dfce-ee65-4686-adac-3c341e09bed3
-- title:
--   Fourier Bridge: fourier seminorm from derivative integrals
-- statement:
--   The Fourier Bridge construction uses the fourier seminorm from derivative integrals property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Mellin/LogProfiles.lean#L790-L809
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Mellin/LogProfiles.lean#L790-L809

import Definitions.Def_OAI_NumberTheory_DirichletL_Mellin_ExponentialSmoothing
import Definitions.Def_OAI_NumberTheory_DirichletL_Mellin_LogProfiles
set_option autoImplicit false
open OAI
open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open scoped ContDiff Manifold
open OAI.FourierBridge

theorem OAI.FourierBridge.fourier_seminorm_from_derivative_integrals
    (g : 𝓢(ℝ, ℂ)) (k : ℕ) :
    (SchwartzMap.seminorm ℝ k 0) (𝓕 g) ≤
      (2 : ℝ) ^ k *
        ∑ p ∈ Finset.range 1 ×ˢ Finset.range (k + 1),
          ∫ v : ℝ, ‖v‖ ^ p.1 * ‖iteratedFDeriv ℝ p.2 g v‖ := by sorry
