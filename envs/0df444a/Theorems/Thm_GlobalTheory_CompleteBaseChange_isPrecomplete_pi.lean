-- Prove2me | Theorems.Thm_GlobalTheory_CompleteBaseChange_isPrecomplete_pi
-- name    : GlobalTheory.CompleteBaseChange.isPrecomplete_pi
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T15:15:35.609013+00:00
-- url     : https://prove2.me/theorems/7b4c0445-4d60-4405-a174-8b21a595ca82
-- title:
--   Complete Base Change: is Precomplete pi
-- statement:
--   The Complete Base Change construction uses the is Precomplete pi property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/ExistsPolynomialSubMem.lean#L32-L40
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/ExistsPolynomialSubMem.lean#L32-L40

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_ExistsPolynomialSubMem
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPowerSeries IsLocalRing
open scoped TensorProduct
open GlobalTheory GlobalTheory.CompleteBaseChange

theorem GlobalTheory.CompleteBaseChange.isPrecomplete_pi {R M : Type*} (ι : Type*) [CommRing R] [AddCommGroup M] [Module R M]
    {J : Ideal R} (hJ : J.FG) [IsPrecomplete J M] : IsPrecomplete J (ι → M) := by sorry
