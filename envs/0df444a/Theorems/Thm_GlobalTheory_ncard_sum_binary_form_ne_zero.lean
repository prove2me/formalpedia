-- Prove2me | Theorems.Thm_GlobalTheory_ncard_sum_binary_form_ne_zero
-- name    : GlobalTheory.ncard_sum_binary_form_ne_zero
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T23:12:38.924173+00:00
-- url     : https://prove2.me/theorems/368ef101-235f-4259-b501-554d8a0ccac9
-- title:
--   Global Theory: ncard sum binary form ne zero
-- statement:
--   The Global Theory construction uses the ncard sum binary form ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/NcardSumBinaryFormNeZero.lean#L157-L192
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/NcardSumBinaryFormNeZero.lean#L157-L192

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
open GlobalTheory
open Finset

theorem GlobalTheory.ncard_sum_binary_form_ne_zero (k : Type) [Field k] [Finite k] (t n : k)
    (hD : t ^ 2 - 4 * n ≠ 0) (η : ℝ) (h1 : (∃ r : k, r ^ 2 - t * r + n = 0) → η = 1)
    (h2 : (¬ ∃ r : k, r ^ 2 - t * r + n = 0) → η = -1) (M : ℕ) :
    ({x : Fin M × Fin 2 → k | ∑ i : Fin M,
        (x (i, 0) ^ 2 + t * x (i, 0) * x (i, 1) + n * x (i, 1) ^ 2) ≠ 0}.ncard : ℝ)
      * (Nat.card k : ℝ)
      = ((Nat.card k : ℝ) - 1) * ((Nat.card k : ℝ) ^ (2 * M) - (η * (Nat.card k : ℝ)) ^ M) := by sorry
