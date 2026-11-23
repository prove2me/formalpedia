-- Prove2me | Theorems.Thm_GlobalTheory_HeckeTheta_norm_hmon
-- name    : GlobalTheory.HeckeTheta.norm_hmon
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T15:07:50.714811+00:00
-- url     : https://prove2.me/theorems/5672ca60-dc29-474a-8793-d022e11de97d
-- title:
--   Hecke Theta: norm hmon
-- statement:
--   The Hecke Theta construction uses the norm hmon property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/GaussZero.lean#L38-L42
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/GaussZero.lean#L38-L42

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_CompletedLStripBounds
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NormWt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_GaussZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField
open GlobalTheory GlobalTheory.HeckeTheta
variable {I : Type} [Fintype I]

theorem GlobalTheory.HeckeTheta.norm_hmon (n : ℤ) (z : ℂ) : ‖hmon n z‖ = ‖z‖ ^ n.natAbs := by sorry
