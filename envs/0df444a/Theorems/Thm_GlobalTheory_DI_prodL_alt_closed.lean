-- Prove2me | Theorems.Thm_GlobalTheory_DI_prodL_alt_closed
-- name    : GlobalTheory.DI.prodL_alt_closed
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T12:35:58.042793+00:00
-- url     : https://prove2.me/theorems/a7aeffd6-a58c-4fc2-9968-ba0942cf3120
-- title:
--   DI: prod L alt closed
-- statement:
--   The DI construction uses the prod L alt closed property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/PublishedTheorems/NadelVanishingPairs/NadelVanishingLemmas/AlternatingProductCocycle.lean#L300-L303
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/PublishedTheorems/NadelVanishingPairs/NadelVanishingLemmas/AlternatingProductCocycle.lean#L300-L303

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

theorem GlobalTheory.DI.prodL_alt_closed : ∀ {K : Type} [CommRing K] {V : Type} [AddCommGroup V] [Module K V] {ι : Type} [LinearOrder ι] (p : ℕ) (d : ExteriorAlgebra K V →+ ExteriorAlgebra K V) (f : ι → V →+ V) (h : ι → ι → V →+ K), IsOddDer d → IsDatum p d f h → (∀ vs : List V, Dtot d (prodL f h vs) = 0 ∧ prodL f h vs ∅ = 0) ∧ ∀ (a : ℕ) (v : Fin a → V), Dtot d (alt f h a v) = 0 ∧ alt f h a v ∅ = 0 := by sorry
