-- Prove2me | Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_JointCompatibilityRateLimit_exists_window_eventually_count_le
-- name    : OAI.MatrixAllFields.MatrixMultiplication.JointCompatibilityRateLimit.exists_window_eventually_count_le
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-11T11:26:03.739066+00:00
-- url     : https://prove2.me/theorems/5a0dc88f-e0ac-4c15-b378-aac2095803eb
-- title:
--   OAI.MatrixAllFields.MatrixMultiplication.JointCompatibilityRateLimit.exists_window_eventually_count_le (OpenAI intermediate lemma)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MatrixAllFields.MatrixMultiplication.AllFieldMain.omega_lt_source_constant`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Staggered extraction for exact matrix multiplication over every field*, OpenAI Math Release, September 24, 2026, result family 107, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.MatrixAllFields.MatrixMultiplication.JointCompatibilityRateLimit.exists_window_eventually_count_le` of [lean/OAI/LinearAlgebra/MatrixFields/Entropy/JointCompatibilityRateLimit.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/LinearAlgebra/MatrixFields/Entropy/JointCompatibilityRateLimit.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MatrixAllFields.MatrixMultiplication.JointCompatibilityRateLimit`, with `open scoped BigOperators Topology Polynomial`, `open MatrixMultiplication.Foundation JointTypeCounts JointCompatibilityIncidence`, `open JointCompatibilityEntropyBound JointCompatibilityScaling Filter`, `open scoped BigOperators Topology`):
--
--   ```lean
--   theorem exists_window_eventually_count_le
--       (base : ∀ c, Shape c → ℕ) (q : ∀ c, Pair c → ℝ)
--       (leftPart : ∀ c, Pair c → Left c) (rightPart : ∀ c, Pair c → Right c)
--       (designatedLeft designatedRight : ∀ c, Shape c → Prop)
--       (leftLaw : ∀ c, Shape c → Left c → ℝ)
--       (rightLaw : ∀ c, Shape c → Right c → ℝ)
--       (hparts : ∀ c, Function.Injective (fun a : Pair c => (leftPart c a, rightPart c a)))
--       (HL HR : (Σ c, Option (Shape c)) → ℝ)
--       {ε ηMax : ℝ} (hε : 0 < ε) (hηMax : 0 < ηMax) :
--       ∃ η : ℝ, 0 < η ∧ η ≤ ηMax ∧
--         ∀ᶠ t : ℕ in atTop,
--           ∀ (Pos : C → Type*) [∀ c, Fintype (Pos c)] [∀ c, DecidableEq (Pos c)]
--             (pairCounts : ∀ c, Pair c → ℕ)
--             (w : FixedClassWords Pos Shape (fun c u => t * base c u))
--             (z : FixedClassWords Pos Pair pairCounts) (χ : ℝ),
--             PairWindow base q Pos pairCounts η →
--             SideEntropyControl Pos Shape Pair Left (fun c u => t * base c u) pairCounts
--               leftPart designatedLeft leftLaw χ HL w →
--             SideEntropyControl Pos Shape Pair Right (fun c u => t * base c u) pairCounts
--               rightPart designatedRight rightLaw χ HR w →
--             (compatibleCandidateCount Pos Shape Pair Left Right (fun c u => t * base c u)
--               pairCounts leftPart rightPart designatedLeft designatedRight leftLaw rightLaw χ z : ℝ) ≤
--               Real.exp ((t : ℝ) *
--                 (compatibilityRate base q designatedLeft designatedRight HL HR + ε)) ∧
--             (0 < compatibleCandidateCount Pos Shape Pair Left Right (fun c u => t * base c u)
--               pairCounts leftPart rightPart designatedLeft designatedRight leftLaw rightLaw χ z →
--               Real.log (compatibleCandidateCount Pos Shape Pair Left Right (fun c u => t * base c u)
--                 pairCounts leftPart rightPart designatedLeft designatedRight leftLaw rightLaw χ z : ℝ) /
--                 (t : ℝ) ≤ compatibilityRate base q designatedLeft designatedRight HL HR + ε)
--   ```
--
--   **Definitions.** The statement is written with `OAI.MatrixAllFields.MatrixMultiplication.JointTypeCounts.FixedClassWords` (definitions bundle `OAIQ254M000` of this split); `OAI.MatrixAllFields.MatrixMultiplication.JointCompatibilityRateLimit.PairWindow` (definitions bundle `OAIQ254M001` of this split); `OAI.MatrixAllFields.MatrixMultiplication.JointCompatibilityIncidence.SideEntropyControl`, `OAI.MatrixAllFields.MatrixMultiplication.JointCompatibilityIncidence.compatibleCandidateCount` and `OAI.MatrixAllFields.MatrixMultiplication.JointCompatibilityRateLimit.compatibilityRate` (definitions bundle `OAIQ254M003` of this split).
--
--   **Used by.** The proof of `OAI.MatrixAllFields.MatrixMultiplication.JointCompatibilityCountProducer.exists_widths_eventually_count_le` of this split imports it.
-- source:
--   OpenAI, Staggered extraction for exact matrix multiplication over every field, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 107; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Staggered-extraction-for-exact-matrix-multiplication-over-every-field-September-24-2026/Staggered-extraction-for-exact-matrix-multiplication-over-every-field-September-24-2026.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/LinearAlgebra/MatrixFields/Entropy/JointCompatibilityRateLimit.lean (declaration OAI.MatrixAllFields.MatrixMultiplication.JointCompatibilityRateLimit.exists_window_eventually_count_le)

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

namespace MatrixMultiplication.JointCompatibilityRateLimit

open MatrixMultiplication.Foundation JointTypeCounts JointCompatibilityIncidence
open JointCompatibilityEntropyBound JointCompatibilityScaling Filter
open scoped BigOperators Topology

attribute [local instance] Classical.propDecidable

variable {C : Type*} [Fintype C] [DecidableEq C]
  {Shape Pair Left Right : C → Type*}
  [∀ c, Fintype (Shape c)] [∀ c, DecidableEq (Shape c)]
  [∀ c, Fintype (Pair c)] [∀ c, DecidableEq (Pair c)]
  [∀ c, Fintype (Left c)] [∀ c, DecidableEq (Left c)]
  [∀ c, Fintype (Right c)] [∀ c, DecidableEq (Right c)]

theorem exists_window_eventually_count_le
    (base : ∀ c, Shape c → ℕ) (q : ∀ c, Pair c → ℝ)
    (leftPart : ∀ c, Pair c → Left c) (rightPart : ∀ c, Pair c → Right c)
    (designatedLeft designatedRight : ∀ c, Shape c → Prop)
    (leftLaw : ∀ c, Shape c → Left c → ℝ)
    (rightLaw : ∀ c, Shape c → Right c → ℝ)
    (hparts : ∀ c, Function.Injective (fun a : Pair c => (leftPart c a, rightPart c a)))
    (HL HR : (Σ c, Option (Shape c)) → ℝ)
    {ε ηMax : ℝ} (hε : 0 < ε) (hηMax : 0 < ηMax) :
    ∃ η : ℝ, 0 < η ∧ η ≤ ηMax ∧
      ∀ᶠ t : ℕ in atTop,
        ∀ (Pos : C → Type*) [∀ c, Fintype (Pos c)] [∀ c, DecidableEq (Pos c)]
          (pairCounts : ∀ c, Pair c → ℕ)
          (w : FixedClassWords Pos Shape (fun c u => t * base c u))
          (z : FixedClassWords Pos Pair pairCounts) (χ : ℝ),
          PairWindow base q Pos pairCounts η →
          SideEntropyControl Pos Shape Pair Left (fun c u => t * base c u) pairCounts
            leftPart designatedLeft leftLaw χ HL w →
          SideEntropyControl Pos Shape Pair Right (fun c u => t * base c u) pairCounts
            rightPart designatedRight rightLaw χ HR w →
          (compatibleCandidateCount Pos Shape Pair Left Right (fun c u => t * base c u)
            pairCounts leftPart rightPart designatedLeft designatedRight leftLaw rightLaw χ z : ℝ) ≤
            Real.exp ((t : ℝ) *
              (compatibilityRate base q designatedLeft designatedRight HL HR + ε)) ∧
          (0 < compatibleCandidateCount Pos Shape Pair Left Right (fun c u => t * base c u)
            pairCounts leftPart rightPart designatedLeft designatedRight leftLaw rightLaw χ z →
            Real.log (compatibleCandidateCount Pos Shape Pair Left Right (fun c u => t * base c u)
              pairCounts leftPart rightPart designatedLeft designatedRight leftLaw rightLaw χ z : ℝ) /
              (t : ℝ) ≤ compatibilityRate base q designatedLeft designatedRight HL HR + ε) := by
  sorry

end MatrixMultiplication.JointCompatibilityRateLimit

end
end

end MatrixAllFields

end OAI
end
