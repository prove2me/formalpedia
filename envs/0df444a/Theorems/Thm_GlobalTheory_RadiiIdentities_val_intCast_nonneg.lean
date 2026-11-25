-- Prove2me | Theorems.Thm_GlobalTheory_RadiiIdentities_val_intCast_nonneg
-- name    : GlobalTheory.RadiiIdentities.val_intCast_nonneg
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T00:25:36.118785+00:00
-- url     : https://prove2.me/theorems/a5a8d456-0c91-43a8-962c-6fe8a2afdc78
-- title:
--   Radii Identities: val int Cast nonneg
-- statement:
--   The Radii Identities construction uses the val int Cast nonneg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/RadiiValuationDifferences.lean#L83-L89
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/RadiiValuationDifferences.lean#L83-L89

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_BiadditiveInSingleVariables
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_RadiiValuationDifferences
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds
open GlobalTheory
open GlobalTheory.RadiiIdentities

theorem GlobalTheory.RadiiIdentities.val_intCast_nonneg {C : Type} [Field C] (v : AddValuation C (WithTop ℝ)) (n : ℤ) :
    0 ≤ v (n : C) := by sorry
