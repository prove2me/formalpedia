-- Prove2me | Theorems.Thm_OAI_FourierBridge_derivative_scale_absorption
-- name    : OAI.FourierBridge.derivative_scale_absorption
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T22:14:39.745516+00:00
-- url     : https://prove2.me/theorems/f6cd9af2-bb68-430d-9c18-6da55f0d2bc2
-- title:
--   Fourier Bridge: derivative scale absorption
-- statement:
--   The Fourier Bridge construction uses the derivative scale absorption property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Mellin/LogProfiles.lean#L591-L625
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Mellin/LogProfiles.lean#L591-L625

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

theorem OAI.FourierBridge.derivative_scale_absorption
    (R u m H CF : ℝ) (A n j : ℕ)
    (hR : 0 ≤ R) (hm : 0 < m)
    (_hH : 0 ≤ H) (hCF : 0 ≤ CF)
    (hu : 0 ≤ u) (hlower : m * (1 + R) ≤ 1 + u)
    (hj : j ≤ n) :
    m ^ (A + n) * (1 + R) ^ A *
      ((j.factorial : ℝ) * (CF / (1 + u) ^ (A + n)) *
        (H ^ 2 * (1 + R)) ^ j) ≤
      (j.factorial : ℝ) * CF * (H ^ 2) ^ j := by sorry
