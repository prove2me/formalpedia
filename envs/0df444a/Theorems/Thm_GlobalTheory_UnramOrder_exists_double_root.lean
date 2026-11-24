-- Prove2me | Theorems.Thm_GlobalTheory_UnramOrder_exists_double_root
-- name    : GlobalTheory.UnramOrder.exists_double_root
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T21:47:18.741358+00:00
-- url     : https://prove2.me/theorems/9b6ae8da-f393-4a7b-9ff3-73c7945ac65e
-- title:
--   Unram Order: exists double root
-- statement:
--   The Unram Order construction uses the exists double root property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/IsPrincipalIdealRingOfHenselian.lean#L202-L215
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/IsPrincipalIdealRingOfHenselian.lean#L202-L215

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsEqTransposeMulMapOfIdempotent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsPrincipalIdealRingOfHenselian
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical
open GlobalTheory GlobalTheory.UnramOrder
open IsLocalRing Polynomial

theorem GlobalTheory.UnramOrder.exists_double_root {k : Type*} [Field k] [Finite k] {t n : k} (h : t ^ 2 - 4 * n = 0) :
    ∃ a, t = 2 * a ∧ n = a ^ 2 := by sorry
