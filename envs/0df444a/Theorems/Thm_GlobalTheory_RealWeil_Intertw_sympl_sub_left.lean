-- Prove2me | Theorems.Thm_GlobalTheory_RealWeil_Intertw_sympl_sub_left
-- name    : GlobalTheory.RealWeil.Intertw.sympl_sub_left
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T19:15:20.914975+00:00
-- url     : https://prove2.me/theorems/dfda9d57-c9c6-4ebb-b71f-7171e26c8129
-- title:
--   Intertw: sympl sub left
-- statement:
--   The Intertw construction uses the sympl sub left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/IntertwiningSymplecticAndGroupLaw.lean#L27-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/IntertwiningSymplecticAndGroupLaw.lean#L27-L31

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_RealMetaplecticRepresentation
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ExistsSchwartzTranslate
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_GaussianSchwartz
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IntertwiningSymplecticAndGroupLaw
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory.RealWeil MeasureTheory Complex
open scoped SchwartzMap Matrix Real RealInnerProductSpace
open GlobalTheory GlobalTheory.RealWeil GlobalTheory.RealWeil.Intertw
variable {l : Type} [Fintype l]

theorem GlobalTheory.RealWeil.Intertw.sympl_sub_left (u u' z : l ⊕ l → ℝ) : sympl (u - u') z = sympl u z - sympl u' z := by sorry
