-- Prove2me | Theorems.Thm_OAI_SharpRamseyFive_ProjectiveRichLines_quantitative_card_mul_le
-- name    : OAI.SharpRamseyFive.ProjectiveRichLines.quantitative_card_mul_le
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-27T23:47:02.686312+00:00
-- url     : https://prove2.me/theorems/6aaabe3e-a01b-4057-9d91-fb3532ba5b69
-- title:
--   OAI.SharpRamseyFive.ProjectiveRichLines.quantitative_card_mul_le: intermediate lemma from OpenAI, Sharp logarithmic exponents for fixed off-diagonal Ramsey numbers (result family 170)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.SharpRamseyFive.main`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Sharp logarithmic exponents for fixed off-diagonal Ramsey numbers (result family 170)*, OpenAI Math Release, September 24, 2026, result family 170, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.SharpRamseyFive.ProjectiveRichLines.quantitative_card_mul_le` of [lean/OAI/Combinatorics/RamseyFive/Geometry/CardMul.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/RamseyFive/Geometry/CardMul.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.SharpRamseyFive.ProjectiveRichLines`, with `open MeasureTheory ProbabilityTheory`, `open scoped BigOperators NNReal`, `open MeasureTheory ProbabilityTheory`, `open scoped BigOperators NNReal`, `open scoped BigOperators`, `open MeasureTheory ProbabilityTheory`, `open scoped BigOperators ENNReal NNReal`, `open Module`, `open scoped LinearAlgebra.Projectivization Classical`):
--
--   ```lean
--   theorem quantitative_card_mul_le {q : ℕ} [CharP L q] (h2 : (2:L) ≠ 0)
--       (hI : Fintype.card I = 4 ∨ Fintype.card I = 5)
--       (p : ι → ℙ K (I → K)) (hp : Function.Injective p)
--       (W : J → Submodule K (I → K)) (hW : ∀ l, finrank K (W l) = 2)
--       (hWinj : Function.Injective W)
--       (M Kp : ℕ) (hM2 : 2 ≤ M) (hMN : M ≤ Fintype.card ι)
--       (hM : ∀ l, M ≤ (Finset.univ.filter (fun i => (p i).rep ∈ W l)).card)
--       (hcap : ∀ U : Submodule K (I → K), finrank K U = 3 →
--         (Finset.univ.filter (fun i => (p i).rep ∈ U)).card ≤ Kp)
--       (hlarge : (1024:ℝ)^2*Fintype.card ι ≤ (M:ℝ)^3)
--       (hchar : 51*Real.sqrt ((Fintype.card ι:ℝ)/M) < q)
--       (hKM : 8*Kp ≤ M^2) :
--       Fintype.card J*M ≤ 20814*Fintype.card ι
--   ```
--
--   **Used by.** The proofs of `OAI.SharpRamseyFive.ScoreGeometry.eventually_high_peel_exceptions`, `OAI.SharpRamseyFive.ScoreGeometry.eventually_literal_plane_exceptions`, `OAI.SharpRamseyFive.ScoreGeometry.eventually_literal_plane_global_trunc` and `OAI.SharpRamseyFive.ScoreGeometry.eventually_literal_plane_half_exceptions` of this split import it.
-- source:
--   OpenAI, Sharp logarithmic exponents for fixed off-diagonal Ramsey numbers (result family 170), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 170; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Sharp-Logarithmic-Exponents-for-Fixed-Off-Diagonal-Ramsey-Numbers-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/RamseyFive/Geometry/CardMul.lean (declaration OAI.SharpRamseyFive.ProjectiveRichLines.quantitative_card_mul_le)

import Mathlib

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
open scoped BigOperators
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal
namespace SharpRamseyFive.ProjectiveRichLines
open Module
open scoped LinearAlgebra.Projectivization Classical
variable {K L I ι J : Type*} [Field K] [Field L] [Algebra K L]
    [IsAlgClosed L] [Fintype I] [Fintype ι] [Nonempty ι] [Fintype J]

theorem quantitative_card_mul_le {q : ℕ} [CharP L q] (h2 : (2:L) ≠ 0)
    (hI : Fintype.card I = 4 ∨ Fintype.card I = 5)
    (p : ι → ℙ K (I → K)) (hp : Function.Injective p)
    (W : J → Submodule K (I → K)) (hW : ∀ l, finrank K (W l) = 2)
    (hWinj : Function.Injective W)
    (M Kp : ℕ) (hM2 : 2 ≤ M) (hMN : M ≤ Fintype.card ι)
    (hM : ∀ l, M ≤ (Finset.univ.filter (fun i => (p i).rep ∈ W l)).card)
    (hcap : ∀ U : Submodule K (I → K), finrank K U = 3 →
      (Finset.univ.filter (fun i => (p i).rep ∈ U)).card ≤ Kp)
    (hlarge : (1024:ℝ)^2*Fintype.card ι ≤ (M:ℝ)^3)
    (hchar : 51*Real.sqrt ((Fintype.card ι:ℝ)/M) < q)
    (hKM : 8*Kp ≤ M^2) :
    Fintype.card J*M ≤ 20814*Fintype.card ι := by
  sorry
end SharpRamseyFive.ProjectiveRichLines

end OAI
end
