-- Prove2me | Theorems.Thm_GlobalTheory_DI_PhiClosed_d_alg_pow
-- name    : GlobalTheory.DI.PhiClosed.d_alg_pow
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T12:34:10.257797+00:00
-- url     : https://prove2.me/theorems/0117bf8e-f99b-4c8f-b348-91cf597ae26e
-- title:
--   Phi Closed: d alg pow
-- statement:
--   The Phi Closed construction uses the d alg pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/PublishedTheorems/NadelVanishingPairs/NadelVanishingLemmas/FrobeniusSplittingClosed.lean#L11-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/PublishedTheorems/NadelVanishingPairs/NadelVanishingLemmas/FrobeniusSplittingClosed.lean#L11-L22

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsFlatLift
import Definitions.Def_Development_WeilBound_CoreStatements_PublishedTheorems_NadelVanishingPairs_NadelVanishingLemmas_AlternatingProductCocycle
import Definitions.Def_Development_WeilBound_CoreStatements_PublishedTheorems_NadelVanishingPairs_NadelVanishingLemmas_FrobeniusSplittingClosed
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.DI
open GlobalTheory GlobalTheory.DI GlobalTheory.DI.PhiClosed
variable {K : Type} [CommRing K] {V : Type} [AddCommGroup V] [Module K V] {ι : Type} [LinearOrder ι]

theorem GlobalTheory.DI.PhiClosed.d_alg_pow (d : ExteriorAlgebra K V →+ ExteriorAlgebra K V) (hd : IsOddDer d) (c : K) (n : ℕ) :
    d (algebraMap K (ExteriorAlgebra K V) c ^ (n + 1)) =
      (n + 1) • (algebraMap K (ExteriorAlgebra K V) c ^ n * d (algebraMap K (ExteriorAlgebra K V) c)) := by sorry
