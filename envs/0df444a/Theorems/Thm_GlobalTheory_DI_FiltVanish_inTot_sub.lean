-- Prove2me | Theorems.Thm_GlobalTheory_DI_FiltVanish_inTot_sub
-- name    : GlobalTheory.DI.FiltVanish.inTot_sub
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T12:35:06.342139+00:00
-- url     : https://prove2.me/theorems/f3fa799f-09c7-4f88-bd8e-a039fdab38dd
-- title:
--   Filt Vanish: in Tot sub
-- statement:
--   The Filt Vanish construction uses the in Tot sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/PublishedTheorems/NadelVanishingPairs/NadelVanishingLemmas/CechVanishingAlongFiltration.lean#L24-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/PublishedTheorems/NadelVanishingPairs/NadelVanishingLemmas/CechVanishingAlongFiltration.lean#L24-L29

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsFlatLift
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CechAndTotalDifferentialAdditiveSquareZeroStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsTotalCochainOfDegreeSuccOfDifferentialsStatement
import Definitions.Def_Development_WeilBound_CoreStatements_PublishedTheorems_NadelVanishingPairs_NadelVanishingLemmas_CechVanishingAlongFiltration
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
open GlobalTheory GlobalTheory.DI
open GlobalTheory GlobalTheory.DI GlobalTheory.DI.FiltVanish
variable {ι : Type} {E : Type} [AddCommGroup E]

theorem GlobalTheory.DI.FiltVanish.inTot_sub {T : ℕ → Finset ι → AddSubgroup E} {m : ℕ} {c c' : Finset ι → E}
    (h1 : InTot T m c) (h2 : InTot T m c') : InTot T m (c - c') := by sorry
