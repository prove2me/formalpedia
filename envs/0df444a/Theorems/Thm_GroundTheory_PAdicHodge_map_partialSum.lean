-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_map_partialSum
-- name    : GroundTheory.PAdicHodge.map_partialSum
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T23:46:55.855801+00:00
-- url     : https://prove2.me/theorems/538113aa-2a97-498b-ab4a-84adf7f5345c
-- title:
--   PAdic Hodge: map partial Sum
-- statement:
--   The PAdic Hodge construction uses the map partial Sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/BdRSeries.lean#L172-L178
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/BdRSeries.lean#L172-L178

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_BdRSeries
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.PAdicHodge
open PowerSeries
variable {B : Type*} [CommRing B] (I : Ideal B)
variable [Algebra ℚ B]
variable [IsAdicComplete I B]
variable {I}
omit [IsAdicComplete I B]

theorem GroundTheory.PAdicHodge.map_partialSum {B' : Type*} [CommRing B'] [Algebra ℚ B'] (F : B →+* B') (z : B)
    (f : ℚ⟦X⟧) (n : ℕ) :
    F (∑ i ∈ Finset.range n, algebraMap ℚ B (coeff i f) * z ^ i) =
      ∑ i ∈ Finset.range n, algebraMap ℚ B' (coeff i f) * F z ^ i := by sorry
