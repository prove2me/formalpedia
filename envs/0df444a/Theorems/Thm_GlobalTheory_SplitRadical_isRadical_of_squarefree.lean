-- Prove2me | Theorems.Thm_GlobalTheory_SplitRadical_isRadical_of_squarefree
-- name    : GlobalTheory.SplitRadical.isRadical_of_squarefree
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T23:01:33.137778+00:00
-- url     : https://prove2.me/theorems/b999afc7-8365-4e5e-a386-1b14aabf4087
-- title:
--   Split Radical: is Radical of squarefree
-- statement:
--   The Split Radical construction uses the is Radical of squarefree property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/IsRadicalSpanPrimeOfNcardPrimesOverEqFinrank.lean#L7-L15
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/IsRadicalSpanPrimeOfNcardPrimesOverEqFinrank.lean#L7-L15

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsRadicalSpanPrimeOfNcardPrimesOverEqFinrank
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField UniqueFactorizationMonoid
open GlobalTheory GlobalTheory.SplitRadical

theorem GlobalTheory.SplitRadical.isRadical_of_squarefree {S : Type} [CommRing S] [IsDedekindDomain S] {I : Ideal S}
    (hI : Squarefree I) : I.IsRadical := by sorry
