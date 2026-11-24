-- Prove2me | Theorems.Thm_GlobalTheory_BinaryFormCount_card_zero
-- name    : GlobalTheory.BinaryFormCount.card_zero
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T13:03:41.86487+00:00
-- url     : https://prove2.me/theorems/f6d8ed98-06a6-49de-a020-7005166f290a
-- title:
--   Binary Form Count: card zero
-- statement:
--   The Binary Form Count construction uses the card zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/NcardSumBinaryFormNeZero.lean#L38-L97
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/NcardSumBinaryFormNeZero.lean#L38-L97

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

theorem GlobalTheory.BinaryFormCount.card_zero {t n : k} (hD : t ^ 2 - 4 * n ≠ 0) {η : ℝ}
    (h1 : (∃ r : k, r ^ 2 - t * r + n = 0) → η = 1)
    (h2 : (¬ ∃ r : k, r ^ 2 - t * r + n = 0) → η = -1) :
    (#{p : k × k | p.1 ^ 2 + t * p.1 * p.2 + n * p.2 ^ 2 = 0} : ℝ)
      = Fintype.card k - η + η * Fintype.card k := by sorry
