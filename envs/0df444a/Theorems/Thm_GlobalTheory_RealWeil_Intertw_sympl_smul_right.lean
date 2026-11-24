-- Prove2me | Theorems.Thm_GlobalTheory_RealWeil_Intertw_sympl_smul_right
-- name    : GlobalTheory.RealWeil.Intertw.sympl_smul_right
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T19:15:30.724658+00:00
-- url     : https://prove2.me/theorems/dbd1f83d-c9ad-42bc-9d95-3c8b10c742f2
-- title:
--   Intertw: sympl smul right
-- statement:
--   The Intertw construction uses the sympl smul right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/IntertwiningSymplecticAndGroupLaw.lean#L19-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/IntertwiningSymplecticAndGroupLaw.lean#L19-L21

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

theorem GlobalTheory.RealWeil.Intertw.sympl_smul_right (r : ℝ) (w w' : l ⊕ l → ℝ) : sympl w (r • w') = r * sympl w w' := by sorry
