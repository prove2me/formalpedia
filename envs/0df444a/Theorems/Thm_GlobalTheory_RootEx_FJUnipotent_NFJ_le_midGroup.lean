-- Prove2me | Theorems.Thm_GlobalTheory_RootEx_FJUnipotent_NFJ_le_midGroup
-- name    : GlobalTheory.RootEx.FJUnipotent.NFJ_le_midGroup
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T19:26:10.25362+00:00
-- url     : https://prove2.me/theorems/2ab3d566-415c-4a78-b9cd-0be569ad6afe
-- title:
--   FJUnipotent: NFJ le mid Group
-- statement:
--   The FJUnipotent construction uses the NFJ le mid Group property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/FourierJacobiUnipotentEqProdRootExchange.lean#L24-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/FourierJacobiUnipotentEqProdRootExchange.lean#L24-L33

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_FourierJacobiAverage
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_UnipotentRadicalBasic
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IntegrableOfMemSB
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_FourierJacobiUnipotentEqProdRootExchange
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage
open GlobalTheory GlobalTheory.RootEx GlobalTheory.RootEx.FJUnipotent
open GlobalTheory.RootEx.Radical
variable {k : Type} [Field k] {n : Type} [Fintype n] [DecidableEq n] {c : ℕ}

theorem GlobalTheory.RootEx.FJUnipotent.NFJ_le_midGroup (ρ : ℕ) : NFJ k n c ρ ≤ midGroup k n c ρ := by sorry
