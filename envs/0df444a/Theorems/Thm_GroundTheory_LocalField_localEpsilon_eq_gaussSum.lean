-- Prove2me | Theorems.Thm_GroundTheory_LocalField_localEpsilon_eq_gaussSum
-- name    : GroundTheory.LocalField.localEpsilon_eq_gaussSum
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T10:20:34.20213+00:00
-- url     : https://prove2.me/theorems/f1db809a-7dc2-5d90-a608-03bcb6249f0c
-- title:
--   Local Field: local Epsilon eq gauss Sum
-- statement:
--   The Local Field construction uses the local Epsilon eq gauss Sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/LocalZetaGauss.lean#L181-L239
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/LocalZetaGauss.lean#L181-L239

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_LocalZetaEpsilon
import Definitions.Def_GroundTheory_LocalFields_LocalZetaGauss
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.LocalField
open ValuativeRel MeasureTheory Measure Topology Filter
open scoped WithZero NNReal ENNReal Pointwise
variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
variable [MeasurableSpace K] [BorelSpace K]
variable {χ : Kˣ →* ℂˣ} {ψ : AddChar K Circle}

theorem GroundTheory.LocalField.localEpsilon_eq_gaussSum (hψ : Continuous ψ) (hψ1 : ψ ≠ 1) (hχ : Continuous χ)
    (hr : ¬ IsUnramifiedChar χ) (s : ℂ) :
    localEpsilon χ ψ s =
      (residueCard K : ℂ) ^ (((addCharConductor ψ - quasiCharConductor χ : ℤ) : ℂ) * s -
        (addCharConductor ψ : ℂ) / 2) * gaussSum χ ψ := by sorry
