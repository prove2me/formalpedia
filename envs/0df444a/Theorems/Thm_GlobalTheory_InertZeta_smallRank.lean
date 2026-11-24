-- Prove2me | Theorems.Thm_GlobalTheory_InertZeta_smallRank
-- name    : GlobalTheory.InertZeta.smallRank
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T17:21:04.434423+00:00
-- url     : https://prove2.me/theorems/209ff200-13de-4150-9ea6-8ce4a2230afd
-- title:
--   Inert Zeta: small Rank
-- statement:
--   The Inert Zeta construction uses the small Rank property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/UnitaryRankLeOneIntegralPoints.lean#L10-L68
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/UnitaryRankLeOneIntegralPoints.lean#L10-L68

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_HasLenOfLatLen
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_UnitaryRankLeOneIntegralPoints
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism.UG Matrix GlobalTheory.SatakeWeyl
open GlobalTheory GlobalTheory.InertZeta

theorem GlobalTheory.InertZeta.smallRank : SmallRank := by sorry
