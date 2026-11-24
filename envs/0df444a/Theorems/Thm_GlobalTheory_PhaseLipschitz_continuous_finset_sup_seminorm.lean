-- Prove2me | Theorems.Thm_GlobalTheory_PhaseLipschitz_continuous_finset_sup_seminorm
-- name    : GlobalTheory.PhaseLipschitz.continuous_finset_sup_seminorm
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T18:48:36.738264+00:00
-- url     : https://prove2.me/theorems/7f4c055b-0623-4e08-9110-6238c278a792
-- title:
--   Phase Lipschitz: continuous finset sup seminorm
-- statement:
--   The Phase Lipschitz construction uses the continuous finset sup seminorm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SchwartzCharacterSeminormBound.lean#L155-L165
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SchwartzCharacterSeminormBound.lean#L155-L165

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

theorem GlobalTheory.PhaseLipschitz.continuous_finset_sup_seminorm {E ι : Type} [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
    {p : ι → Seminorm ℂ E} (hp : ∀ i, Continuous (p i)) (s : Finset ι) :
    Continuous ⇑(s.sup p : Seminorm ℂ E) := by sorry
