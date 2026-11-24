-- Prove2me | Theorems.Thm_GlobalTheory_DI_AltClosed_dtot_oneC
-- name    : GlobalTheory.DI.AltClosed.dtot_oneC
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T12:34:33.587842+00:00
-- url     : https://prove2.me/theorems/093e1478-e8f6-4f85-9452-d79128c82d1e
-- title:
--   Alt Closed: dtot one C
-- statement:
--   The Alt Closed construction uses the dtot one C property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/PublishedTheorems/NadelVanishingPairs/NadelVanishingLemmas/AlternatingProductCocycle.lean#L96-L101
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/PublishedTheorems/NadelVanishingPairs/NadelVanishingLemmas/AlternatingProductCocycle.lean#L96-L101

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsFlatLift
import Definitions.Def_Development_WeilBound_CoreStatements_PublishedTheorems_NadelVanishingPairs_NadelVanishingLemmas_AlternatingProductCocycle
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
open GlobalTheory GlobalTheory.DI GlobalTheory.DI.AltClosed
variable {K : Type} [CommRing K] {V : Type} [AddCommGroup V] [Module K V] {ι : Type} [LinearOrder ι]

theorem GlobalTheory.DI.AltClosed.dtot_oneC (d : ExteriorAlgebra K V →+ ExteriorAlgebra K V) (hd : IsOddDer d) :
    Dtot d (oneC : Finset ι → ExteriorAlgebra K V) = 0 := by sorry
