-- Prove2me | Theorems.Thm_OAI_CommonBasesFPRAS_rational_algorithm_success
-- name    : OAI.CommonBasesFPRAS.rational_algorithm_success
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-26T01:27:09.740835+00:00
-- url     : https://prove2.me/theorems/aa5e9a25-a5df-4927-b8d8-c36a962583e5
-- title:
--   OAI.CommonBasesFPRAS.rational_algorithm_success: intermediate lemma from OpenAI, Approximate counting of common bases of two matroids
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.common_bases_fpras`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Approximate counting of common bases of two matroids*, OpenAI Math Release, September 23, 2026, result family 114, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.CommonBasesFPRAS.rational_algorithm_success` of [lean/OAI/Combinatorics/MatroidCounting/MatroidCounting/CommonBases.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/MatroidCounting/MatroidCounting/CommonBases.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.CommonBasesFPRAS`, with `open scoped BigOperators Classical`, `open scoped BigOperators Classical`):
--
--   ```lean
--   theorem rational_algorithm_success (hE₁ : M₁.E=Set.univ) (hE₂ : M₂.E=Set.univ)
--       (hr : M₁.eRank=M₂.eRank) (ε : ℚ) (hε0 : 0<ε) (hε1 : ε<1)
--       (b : ℕ) (hb : (1/2:ℝ)^b ≤ (ε:ℝ)/10) (hZ : 0<commonBaseCount M₁ M₂)
--       (hN : (10:ℝ)^10*(annealLength n b+1)*n^14/(annealTolerance (ε:ℝ) (annealLength n b))^2 ≤ N) :
--       3/4 ≤ (rationalAlgorithmTree n hn M₁ M₂ N (annealLength n b)).expectation
--         (DrawTree.optionValue (fun z => if relativeAccuracy ε (commonBaseCount M₁ M₂) z then 1 else 0))
--   ```
--
--   **Definitions.** The statement is written with `OAI.CommonBasesFPRAS.annealLength`, `OAI.CommonBasesFPRAS.annealTolerance`, `OAI.CommonBasesFPRAS.rationalAlgorithmTree`, `OAI.CommonBasesFPRAS.DrawTree.expectation` and `OAI.CommonBasesFPRAS.DrawTree.optionValue` (definitions bundle `OAIQ2Mt000` of this split); `OAI.CommonBasesFPRAS.commonBaseCount` and `OAI.CommonBasesFPRAS.relativeAccuracy` (the published bundle `Def_CommonBasesFPRAS`).
--
--   **Used by.** The proof of `OAI.common_bases_fpras` of this split imports it.
-- source:
--   OpenAI, Approximate counting of common bases of two matroids, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 114; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Approximate-counting-of-common-bases-of-two-matroids-September-23-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/MatroidCounting/MatroidCounting/CommonBases.lean (declaration OAI.CommonBasesFPRAS.rational_algorithm_success)

import Mathlib
import Definitions.Def_CommonBasesFPRAS
import Definitions.Def_OAIQ2Mt000

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CommonBasesFPRAS

section

section

open scoped BigOperators Classical
open scoped BigOperators Classical
variable (n : ℕ) (hn : 0<n) (M₁ M₂ : Matroid (Fin n)) (N L : ℕ)
include hn in
theorem rational_algorithm_success (hE₁ : M₁.E=Set.univ) (hE₂ : M₂.E=Set.univ)
    (hr : M₁.eRank=M₂.eRank) (ε : ℚ) (hε0 : 0<ε) (hε1 : ε<1)
    (b : ℕ) (hb : (1/2:ℝ)^b ≤ (ε:ℝ)/10) (hZ : 0<commonBaseCount M₁ M₂)
    (hN : (10:ℝ)^10*(annealLength n b+1)*n^14/(annealTolerance (ε:ℝ) (annealLength n b))^2 ≤ N) :
    3/4 ≤ (rationalAlgorithmTree n hn M₁ M₂ N (annealLength n b)).expectation
      (DrawTree.optionValue (fun z => if relativeAccuracy ε (commonBaseCount M₁ M₂) z then 1 else 0)) := by
  sorry

end

open scoped BigOperators Classical

open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical

open scoped BigOperators Classical

open scoped Classical

open scoped Classical

open scoped BigOperators Classical

open scoped BigOperators Classical

open scoped BigOperators Classical

open scoped BigOperators Classical

open scoped BigOperators Classical

open scoped Classical

end

namespace MachineCode


open Expression

open Expression

open Expression

open Expression

open Expression

open Expression
end MachineCode

end CommonBasesFPRAS

open CommonBasesFPRAS CommonBasesFPRAS.MachineCode

end OAI
end
