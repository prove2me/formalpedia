-- Prove2me | Theorems.Thm_GroundTheory_LocalField_localZeta_indicator_valBall_of_isUnramified
-- name    : GroundTheory.LocalField.localZeta_indicator_valBall_of_isUnramified
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T10:17:51.852078+00:00
-- url     : https://prove2.me/theorems/00c3bbab-3bd2-4503-9e58-63e553f27b47
-- title:
--   Local Field: local Zeta indicator val Ball of is Unramified
-- statement:
--   The Local Field construction uses the local Zeta indicator val Ball of is Unramified property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/LocalZetaEpsilon.lean#L142-L151
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/LocalZetaEpsilon.lean#L142-L151

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
variable {χ : Kˣ →* ℂˣ}

theorem GroundTheory.LocalField.localZeta_indicator_valBall_of_isUnramified (hχ : Continuous χ) (hu : IsUnramifiedChar χ)
    (k : ℤ) {s : ℂ} (hs : -quasiCharExponent χ < s.re) :
    localZeta ((valBall K k : Set K).indicator fun _ => 1) χ s =
      (((χ (unifUnit K) : ℂˣ) : ℂ) * (residueCard K : ℂ) ^ (-s)) ^ k * localLFactor χ s := by sorry
