-- Prove2me | Theorems.Thm_GlobalTheory_BinaryFormCount_card_sum_zero
-- name    : GlobalTheory.BinaryFormCount.card_sum_zero
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T13:03:42.484707+00:00
-- url     : https://prove2.me/theorems/17e30936-81da-4948-bd13-a6fbf48f9eaa
-- title:
--   Binary Form Count: card sum zero
-- statement:
--   The Binary Form Count construction uses the card sum zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/NcardSumBinaryFormNeZero.lean#L124-L149
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/NcardSumBinaryFormNeZero.lean#L124-L149

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_GlobalSchurBounds_GeneralLinearActions_GenusMassVolumes
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_GlobalSignature_SelfDualUnramifiedPlaces
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsEqTransposeMulMapOfIdempotent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_NcardSumBinaryFormNeZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory GlobalTheory.BinaryFormCount
open Finset
variable {k : Type} [Field k] [Fintype k] [DecidableEq k]

theorem GlobalTheory.BinaryFormCount.card_sum_zero {α : Type} [Fintype α] [DecidableEq α] (Q : α → k) (q η : ℝ)
    (hα : (Fintype.card α : ℝ) = q ^ 2)
    (hQ : ∀ c, (#{p : α | Q p = c} : ℝ) = q - η + if c = 0 then η * q else 0) (M : ℕ) :
    (#{x : Fin M → α | ∑ i, Q (x i) = 0} : ℝ) * q = q ^ (2 * M) + (q - 1) * (η * q) ^ M := by sorry
