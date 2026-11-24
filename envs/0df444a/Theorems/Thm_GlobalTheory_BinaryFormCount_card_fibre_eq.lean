-- Prove2me | Theorems.Thm_GlobalTheory_BinaryFormCount_card_fibre_eq
-- name    : GlobalTheory.BinaryFormCount.card_fibre_eq
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T13:03:39.476302+00:00
-- url     : https://prove2.me/theorems/adf7a60a-2836-45b0-bbf1-4cd829b36618
-- title:
--   Binary Form Count: card fibre eq
-- statement:
--   The Binary Form Count construction uses the card fibre eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/NcardSumBinaryFormNeZero.lean#L15-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/NcardSumBinaryFormNeZero.lean#L15-L36

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

theorem GlobalTheory.BinaryFormCount.card_fibre_eq {t n : k} (hD : t ^ 2 - 4 * n ≠ 0) {c : k} (hc : c ≠ 0) :
    #{p : k × k | p.1 ^ 2 + t * p.1 * p.2 + n * p.2 ^ 2 = c}
      = #{p : k × k | p.1 ^ 2 + t * p.1 * p.2 + n * p.2 ^ 2 = 1} := by sorry
