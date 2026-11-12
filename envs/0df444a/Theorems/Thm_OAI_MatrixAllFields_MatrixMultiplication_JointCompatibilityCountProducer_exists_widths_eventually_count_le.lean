-- Prove2me | Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_JointCompatibilityCountProducer_exists_widths_eventually_count_le
-- name    : OAI.MatrixAllFields.MatrixMultiplication.JointCompatibilityCountProducer.exists_widths_eventually_count_le
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-11T11:26:01.185122+00:00
-- url     : https://prove2.me/theorems/d0c503b2-072a-4eca-bd77-e7937a94ca1f
-- title:
--   OAI.MatrixAllFields.MatrixMultiplication.JointCompatibilityCountProducer.exists_widths_eventually_count_le (OpenAI intermediate lemma)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MatrixAllFields.MatrixMultiplication.AllFieldMain.omega_lt_source_constant`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Staggered extraction for exact matrix multiplication over every field*, OpenAI Math Release, September 24, 2026, result family 107, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.MatrixAllFields.MatrixMultiplication.JointCompatibilityCountProducer.exists_widths_eventually_count_le` of [lean/OAI/LinearAlgebra/MatrixFields/Construction/JointCompatibilityCountProducer.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/LinearAlgebra/MatrixFields/Construction/JointCompatibilityCountProducer.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MatrixAllFields.MatrixMultiplication.JointCompatibilityCountProducer`, with `open scoped BigOperators Topology Polynomial`, `open MatrixMultiplication.Foundation JointTypeCounts JointCompatibilityIncidence`, `open JointCompatibilityControls JointCompatibilityScaling JointCompatibilityRateLimit Filter`, `open scoped BigOperators Topology`):
--
--   ```lean
--   theorem exists_widths_eventually_count_le
--       (base : ∀ c, Shape c → ℕ) (q : ∀ c, Pair c → ℝ)
--       (leftPart : ∀ c, Pair c → Left c) (rightPart : ∀ c, Pair c → Right c)
--       (designatedLeft designatedRight : ∀ c, Shape c → Prop)
--       (leftLaw : ∀ c, Shape c → Left c → ℝ)
--       (rightLaw : ∀ c, Shape c → Right c → ℝ)
--       (hparts : ∀ c, Function.Injective (fun a : Pair c => (leftPart c a, rightPart c a)))
--       (hL0 : ∀ c u a, 0 ≤ leftLaw c u a) (hL1 : ∀ c u a, leftLaw c u a ≤ 1)
--       (hR0 : ∀ c u a, 0 ≤ rightLaw c u a) (hR1 : ∀ c u a, rightLaw c u a ≤ 1)
--       (hleft : ∀ c a, (baseSize base c : ℝ) *
--         (∑ b : {b : Pair c // leftPart c b = a}, q c b.val) =
--           totalCenterCount base leftLaw c a)
--       (hright : ∀ c a, (baseSize base c : ℝ) *
--         (∑ b : {b : Pair c // rightPart c b = a}, q c b.val) =
--           totalCenterCount base rightLaw c a)
--       {ε χMax ηMax : ℝ} (hε : 0 < ε) (hχMax : 0 < χMax) (hηMax : 0 < ηMax) :
--       ∃ χ η : ℝ, 0 < χ ∧ χ ≤ χMax ∧ 0 < η ∧ η ≤ ηMax ∧
--         ∀ᶠ t : ℕ in atTop,
--           ∀ (Pos : C → Type*) [∀ c, Fintype (Pos c)] [∀ c, DecidableEq (Pos c)]
--             (pairCounts : ∀ c, Pair c → ℕ)
--             (_ : FixedClassWords Pos Shape (fun c u => t * base c u))
--             (z : FixedClassWords Pos Pair pairCounts),
--             PairWindow base q Pos pairCounts η →
--             (compatibleCandidateCount Pos Shape Pair Left Right (fun c u => t * base c u)
--               pairCounts leftPart rightPart designatedLeft designatedRight leftLaw rightLaw χ z : ℝ) ≤
--               Real.exp ((t : ℝ) *
--                 (compatibilityRate base q designatedLeft designatedRight
--                   (groupCap base designatedLeft leftLaw 0)
--                   (groupCap base designatedRight rightLaw 0) + ε)) ∧
--             (0 < compatibleCandidateCount Pos Shape Pair Left Right (fun c u => t * base c u)
--               pairCounts leftPart rightPart designatedLeft designatedRight leftLaw rightLaw χ z →
--               Real.log (compatibleCandidateCount Pos Shape Pair Left Right (fun c u => t * base c u)
--                 pairCounts leftPart rightPart designatedLeft designatedRight leftLaw rightLaw χ z : ℝ) /
--                 (t : ℝ) ≤ compatibilityRate base q designatedLeft designatedRight
--                   (groupCap base designatedLeft leftLaw 0)
--                   (groupCap base designatedRight rightLaw 0) + ε)
--   ```
--
--   **Definitions.** The statement is written with `OAI.MatrixAllFields.MatrixMultiplication.JointTypeCounts.FixedClassWords` (definitions bundle `OAIQ254M000` of this split); `OAI.MatrixAllFields.MatrixMultiplication.JointCompatibilityControls.totalCenterCount`, `OAI.MatrixAllFields.MatrixMultiplication.JointCompatibilityRateLimit.PairWindow` and `OAI.MatrixAllFields.MatrixMultiplication.JointCompatibilityScaling.baseSize` (definitions bundle `OAIQ254M001` of this split); `OAI.MatrixAllFields.MatrixMultiplication.JointCompatibilityControls.groupCap`, `OAI.MatrixAllFields.MatrixMultiplication.JointCompatibilityIncidence.compatibleCandidateCount` and `OAI.MatrixAllFields.MatrixMultiplication.JointCompatibilityRateLimit.compatibilityRate` (definitions bundle `OAIQ254M003` of this split).
--
--   **Used by.** The proof of `OAI.MatrixAllFields.MatrixMultiplication.AllFieldGroupCountRate.exists_widths_eventually_nativeCount_le` of this split imports it.
-- source:
--   OpenAI, Staggered extraction for exact matrix multiplication over every field, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 107; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Staggered-extraction-for-exact-matrix-multiplication-over-every-field-September-24-2026/Staggered-extraction-for-exact-matrix-multiplication-over-every-field-September-24-2026.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/LinearAlgebra/MatrixFields/Construction/JointCompatibilityCountProducer.lean (declaration OAI.MatrixAllFields.MatrixMultiplication.JointCompatibilityCountProducer.exists_widths_eventually_count_le)

import Mathlib
import Definitions.Def_OAIQ254M003

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section

namespace MatrixMultiplication.JointCompatibilityCountProducer

open MatrixMultiplication.Foundation JointTypeCounts JointCompatibilityIncidence
open JointCompatibilityControls JointCompatibilityScaling JointCompatibilityRateLimit Filter
open scoped BigOperators Topology

attribute [local instance] Classical.propDecidable

variable {C : Type*} [Fintype C] [DecidableEq C]
  {Shape A : C → Type*}
  [∀ c, Fintype (Shape c)] [∀ c, DecidableEq (Shape c)]
  [∀ c, Fintype (A c)] [∀ c, DecidableEq (A c)]

section CountProducer

variable {Pair Left Right : C → Type*}
  [∀ c, Fintype (Pair c)] [∀ c, DecidableEq (Pair c)]
  [∀ c, Fintype (Left c)] [∀ c, DecidableEq (Left c)]
  [∀ c, Fintype (Right c)] [∀ c, DecidableEq (Right c)]

theorem exists_widths_eventually_count_le
    (base : ∀ c, Shape c → ℕ) (q : ∀ c, Pair c → ℝ)
    (leftPart : ∀ c, Pair c → Left c) (rightPart : ∀ c, Pair c → Right c)
    (designatedLeft designatedRight : ∀ c, Shape c → Prop)
    (leftLaw : ∀ c, Shape c → Left c → ℝ)
    (rightLaw : ∀ c, Shape c → Right c → ℝ)
    (hparts : ∀ c, Function.Injective (fun a : Pair c => (leftPart c a, rightPart c a)))
    (hL0 : ∀ c u a, 0 ≤ leftLaw c u a) (hL1 : ∀ c u a, leftLaw c u a ≤ 1)
    (hR0 : ∀ c u a, 0 ≤ rightLaw c u a) (hR1 : ∀ c u a, rightLaw c u a ≤ 1)
    (hleft : ∀ c a, (baseSize base c : ℝ) *
      (∑ b : {b : Pair c // leftPart c b = a}, q c b.val) =
        totalCenterCount base leftLaw c a)
    (hright : ∀ c a, (baseSize base c : ℝ) *
      (∑ b : {b : Pair c // rightPart c b = a}, q c b.val) =
        totalCenterCount base rightLaw c a)
    {ε χMax ηMax : ℝ} (hε : 0 < ε) (hχMax : 0 < χMax) (hηMax : 0 < ηMax) :
    ∃ χ η : ℝ, 0 < χ ∧ χ ≤ χMax ∧ 0 < η ∧ η ≤ ηMax ∧
      ∀ᶠ t : ℕ in atTop,
        ∀ (Pos : C → Type*) [∀ c, Fintype (Pos c)] [∀ c, DecidableEq (Pos c)]
          (pairCounts : ∀ c, Pair c → ℕ)
          (_ : FixedClassWords Pos Shape (fun c u => t * base c u))
          (z : FixedClassWords Pos Pair pairCounts),
          PairWindow base q Pos pairCounts η →
          (compatibleCandidateCount Pos Shape Pair Left Right (fun c u => t * base c u)
            pairCounts leftPart rightPart designatedLeft designatedRight leftLaw rightLaw χ z : ℝ) ≤
            Real.exp ((t : ℝ) *
              (compatibilityRate base q designatedLeft designatedRight
                (groupCap base designatedLeft leftLaw 0)
                (groupCap base designatedRight rightLaw 0) + ε)) ∧
          (0 < compatibleCandidateCount Pos Shape Pair Left Right (fun c u => t * base c u)
            pairCounts leftPart rightPart designatedLeft designatedRight leftLaw rightLaw χ z →
            Real.log (compatibleCandidateCount Pos Shape Pair Left Right (fun c u => t * base c u)
              pairCounts leftPart rightPart designatedLeft designatedRight leftLaw rightLaw χ z : ℝ) /
              (t : ℝ) ≤ compatibilityRate base q designatedLeft designatedRight
                (groupCap base designatedLeft leftLaw 0)
                (groupCap base designatedRight rightLaw 0) + ε) := by
  sorry

end CountProducer

end MatrixMultiplication.JointCompatibilityCountProducer

end
end

end MatrixAllFields

end OAI
end
