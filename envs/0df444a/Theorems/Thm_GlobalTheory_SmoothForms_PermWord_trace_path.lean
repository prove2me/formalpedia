-- Prove2me | Theorems.Thm_GlobalTheory_SmoothForms_PermWord_trace_path
-- name    : GlobalTheory.SmoothForms.PermWord.trace_path
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T20:18:51.0856+00:00
-- url     : https://prove2.me/theorems/78f598ae-6526-430f-847c-6ba08e94a6ed
-- title:
--   Perm Word: trace path
-- statement:
--   The Perm Word construction uses the trace path property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HeightProofs/PermutationWordGelfandPolynomialModShorter.lean#L19-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HeightProofs/PermutationWordGelfandPolynomialModShorter.lean#L19-L34

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_IsLieDataCircle
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_PermutationWordGelfandPolynomialModShorter
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.SmoothForms NumberField Matrix
open scoped ContDiff Topology
noncomputable section
open GlobalTheory GlobalTheory.SmoothForms GlobalTheory.SmoothForms.PermWord
variable {S : Type} [CommRing S] {n : ℕ}

theorem GlobalTheory.SmoothForms.PermWord.trace_path (X : Matrix (Fin n) (Fin n) S) (k : ℕ) : ∀ Y : Matrix (Fin n) (Fin n) S,
    (Y * X ^ k).trace = ∑ idx : Fin (k + 1) → Fin n,
      Y (idx (Fin.last k)) (idx 0) * ∏ a : Fin k, X (idx a.castSucc) (idx a.succ) := by sorry
