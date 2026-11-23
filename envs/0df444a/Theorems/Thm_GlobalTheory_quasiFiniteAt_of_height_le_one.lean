-- Prove2me | Theorems.Thm_GlobalTheory_quasiFiniteAt_of_height_le_one
-- name    : GlobalTheory.quasiFiniteAt_of_height_le_one
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T15:19:47.01866+00:00
-- url     : https://prove2.me/theorems/12f037b8-076a-4152-9e31-ae1bd0b63bf3
-- title:
--   Global Theory: quasi Finite At of height le one
-- statement:
--   The Global Theory construction uses the quasi Finite At of height le one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ExistsValuationSubringLiftOfSpecialFibre.lean#L66-L104
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ExistsValuationSubringLiftOfSpecialFibre.lean#L66-L104

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsValuationSubringLiftOfSpecialFibre
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing
open GlobalTheory
universe u

theorem GlobalTheory.quasiFiniteAt_of_height_le_one {O B : Type*} [CommRing O] [IsNoetherianRing O]
    [CommRing B] [IsDomain B] [Algebra O B] [Algebra.FiniteType O B]
    (m : Ideal B) [hm : m.IsMaximal] (h1 : m.height ≤ 1) (π : O) (hπ : algebraMap O B π ≠ 0)
    (hπm : algebraMap O B π ∈ m) : Algebra.QuasiFiniteAt O m := by sorry
