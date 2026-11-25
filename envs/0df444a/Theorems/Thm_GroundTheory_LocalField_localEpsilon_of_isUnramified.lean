-- Prove2me | Theorems.Thm_GroundTheory_LocalField_localEpsilon_of_isUnramified
-- name    : GroundTheory.LocalField.localEpsilon_of_isUnramified
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T10:17:36.867964+00:00
-- url     : https://prove2.me/theorems/fa39b986-3ca1-5fb1-9258-9940bffd3b90
-- title:
--   Local Field: local Epsilon of is Unramified
-- statement:
--   The Local Field construction uses the local Epsilon of is Unramified property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/LocalZetaEpsilon.lean#L113-L119
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/LocalZetaEpsilon.lean#L113-L119

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_LocalZetaTate
import Definitions.Def_GroundTheory_LocalFields_PadicLogHom
import Definitions.Def_GroundTheory_LocalFields_LocalZetaEpsilon
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

theorem GroundTheory.LocalField.localEpsilon_of_isUnramified (h : IsUnramifiedChar χ) (s : ℂ) :
    localEpsilon χ ψ s = ((χ (unifUnit K) : ℂˣ) : ℂ) ^ (-addCharConductor ψ) *
      (residueCard K : ℂ) ^ ((addCharConductor ψ : ℂ) * (s - 1 / 2)) := by sorry
