-- Prove2me | Theorems.Thm_GlobalTheory_PhaseLipschitz_norm_psi_le
-- name    : GlobalTheory.PhaseLipschitz.norm_psi_le
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T18:48:49.718006+00:00
-- url     : https://prove2.me/theorems/bfcbde6b-bda7-4589-9588-2fbaf06672b1
-- title:
--   Phase Lipschitz: norm psi le
-- statement:
--   The Phase Lipschitz construction uses the norm psi le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SchwartzCharacterSeminormBound.lean#L25-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SchwartzCharacterSeminormBound.lean#L25-L30

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_MetaplecticRepresentation
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SchwartzSeminormSmulLeftLinearPhaseLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SchwartzCharacterSeminormBound
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped SchwartzMap
open GlobalTheory.Published.Metaplectic
noncomputable section
open GlobalTheory GlobalTheory.PhaseLipschitz

theorem GlobalTheory.PhaseLipschitz.norm_psi_le (k t : ℝ) : ‖psi k t‖ ≤ 2 * Real.pi * |t + k| := by sorry
