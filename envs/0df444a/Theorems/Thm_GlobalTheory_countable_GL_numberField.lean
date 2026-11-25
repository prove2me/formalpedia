-- Prove2me | Theorems.Thm_GlobalTheory_countable_GL_numberField
-- name    : GlobalTheory.countable_GL_numberField
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T02:53:08.655802+00:00
-- url     : https://prove2.me/theorems/60b7c34b-16b8-5842-903b-5d10e4fbde17
-- title:
--   Global Theory: countable GL number Field
-- statement:
--   The Global Theory construction uses the countable GL number Field property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsCandidateBorelMoveOpenFramesBaire.lean#L9-L14
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsCandidateBorelMoveOpenFramesBaire.lean#L9-L14

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_Signature
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsCandidateBorelMoveOpenFramesBaire
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G.FD
open GlobalTheory
noncomputable section

theorem GlobalTheory.countable_GL_numberField {E : Type} [Field E] [NumberField E] (r : ℕ) :
    Countable (GL (Fin r) E) := by sorry
