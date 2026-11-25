-- Prove2me | Theorems.Thm_GroundTheory_LocalField_localZeta_oneAddValBallIndicator_ne_zero
-- name    : GroundTheory.LocalField.localZeta_oneAddValBallIndicator_ne_zero
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T10:17:49.332111+00:00
-- url     : https://prove2.me/theorems/fe79651b-ec41-5b12-af65-d08b9b941a7a
-- title:
--   Local Field: local Zeta one Add Val Ball Indicator ne zero
-- statement:
--   The Local Field construction uses the local Zeta one Add Val Ball Indicator ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/LocalZetaEpsilon.lean#L319-L328
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/LocalZetaEpsilon.lean#L319-L328

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

theorem GroundTheory.LocalField.localZeta_oneAddValBallIndicator_ne_zero {c : ℕ} (hc : 1 ≤ c)
    (hker : unitFiltrationUnits K c ≤ χ.ker) (s : ℂ) :
    localZeta (oneAddValBallIndicator c) χ s ≠ 0 := by sorry
