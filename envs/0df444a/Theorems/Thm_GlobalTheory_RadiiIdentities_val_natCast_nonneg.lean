-- Prove2me | Theorems.Thm_GlobalTheory_RadiiIdentities_val_natCast_nonneg
-- name    : GlobalTheory.RadiiIdentities.val_natCast_nonneg
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T00:22:58.416099+00:00
-- url     : https://prove2.me/theorems/c0d80faa-0d84-4563-92da-6e014208f88b
-- title:
--   Radii Identities: val nat Cast nonneg
-- statement:
--   The Radii Identities construction uses the val nat Cast nonneg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/RadiiValuationDifferences.lean#L72-L81
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/RadiiValuationDifferences.lean#L72-L81

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

theorem GlobalTheory.RadiiIdentities.val_natCast_nonneg {C : Type} [Field C] (v : AddValuation C (WithTop ℝ)) (n : ℕ) :
    0 ≤ v (n : C) := by sorry
