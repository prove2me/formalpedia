-- Prove2me | Theorems.Thm_GlobalTheory_T_flat_quotient_weakly_regular
-- name    : GlobalTheory.T.flat_quotient_weakly_regular
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T20:40:55.707921+00:00
-- url     : https://prove2.me/theorems/a22f3f95-78bc-479d-a0a3-07c65a52503a
-- title:
--   T: flat quotient weakly regular
-- statement:
--   The T construction uses the flat quotient weakly regular property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/FlatQuotientWeaklyRegularStatement.lean#L5-L6
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/FlatQuotientWeaklyRegularStatement.lean#L5-L6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_FlatQuotientWeaklyRegular
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_FlatQuotientWeaklyRegularStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing TensorProduct
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.flat_quotient_weakly_regular : ∀ (V A : Type) [CommRing V] [IsNoetherianRing V] [IsLocalRing V] [CommRing A] [IsNoetherianRing A] [IsLocalRing A] [Algebra V A] [IsLocalHom (algebraMap V A)] [Module.Flat V A] (rs : List A), (∀ r ∈ rs, r ∈ maximalIdeal A) → RingTheory.Sequence.IsWeaklyRegular (A ⧸ (maximalIdeal V).map (algebraMap V A)) rs → Module.Flat V (A ⧸ Ideal.ofList rs) := by sorry
