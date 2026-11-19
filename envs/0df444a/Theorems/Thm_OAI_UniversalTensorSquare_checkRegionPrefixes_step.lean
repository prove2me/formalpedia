-- Prove2me | Theorems.Thm_OAI_UniversalTensorSquare_checkRegionPrefixes_step
-- name    : OAI.UniversalTensorSquare.checkRegionPrefixes_step
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-19T00:27:13.42073+00:00
-- url     : https://prove2.me/theorems/2386e4f2-cfb0-429c-aa79-311ca1b580d9
-- title:
--   OAI.UniversalTensorSquare.checkRegionPrefixes_step: intermediate lemma from OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.UniversalTensorSquares.universal_tensor_square`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Universal Tensor Squares for Symmetric Groups (result family 205)*, OpenAI Math Release, September 24, 2026, result family 205, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.UniversalTensorSquare.checkRegionPrefixes_step` of [lean/OAI/RepresentationTheory/UniversalSquare/Support/SplitUnionRowChecker.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Support/SplitUnionRowChecker.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.UniversalTensorSquare`):
--
--   ```lean
--   lemma checkRegionPrefixes_step (P : List ℕ → Bool) (k n upper : ℕ)
--       (regions : List PrefixRegion) (pref : List ℕ)
--       (hc : ∀ a, max 1 (n/(k+1)) ≤ a → a ≤ min n upper → n ≤ (k+1)*a →
--         checkRegionPrefixes P k (n-a) a
--           (nextRegions a (liveRegions (k+1) n upper regions)) (a::pref) = true) :
--       checkRegionPrefixes P (k+1) n upper regions pref = true
--   ```
--
--   **Definitions.** The statement is written with `OAI.UniversalTensorSquare.PrefixRegion`, `OAI.UniversalTensorSquare.checkRegionPrefixes`, `OAI.UniversalTensorSquare.liveRegions` and `OAI.UniversalTensorSquare.nextRegions` (definitions bundle `OAIQ259US001` of this split).
--
--   **Used by.** The proofs of `OAI.UniversalTensorSquare.degreeUnionBranch62_1286`, `OAI.UniversalTensorSquare.degreeUnionBranch62_166`, `OAI.UniversalTensorSquare.degreeUnionBranch62_188`, `OAI.UniversalTensorSquare.degreeUnionBranch62_218`, `OAI.UniversalTensorSquare.degreeUnionBranch62_243`, `OAI.UniversalTensorSquare.degreeUnionBranch62_278`, `OAI.UniversalTensorSquare.degreeUnionBranch62_293`, `OAI.UniversalTensorSquare.degreeUnionBranch62_299`, `OAI.UniversalTensorSquare.degreeUnionBranch62_315`, `OAI.UniversalTensorSquare.degreeUnionBranch62_321`, `OAI.UniversalTensorSquare.degreeUnionBranch62_345`, `OAI.UniversalTensorSquare.degreeUnionBranch62_351`, `OAI.UniversalTensorSquare.degreeUnionBranch62_369`, `OAI.UniversalTensorSquare.degreeUnionBranch62_414`, `OAI.UniversalTensorSquare.degreeUnionBranch62_429`, `OAI.UniversalTensorSquare.degreeUnionBranch62_435`, `OAI.UniversalTensorSquare.degreeUnionBranch62_451`, `OAI.UniversalTensorSquare.degreeUnionBranch62_457`, `OAI.UniversalTensorSquare.degreeUnionBranch62_689`, `OAI.UniversalTensorSquare.degreeUnionBranch62_759`, `OAI.UniversalTensorSquare.degreeUnionBranch62_812`, `OAI.UniversalTensorSquare.degreeUnionBranch62_848`, `OAI.UniversalTensorSquare.degreeUnionBranch62_863`, `OAI.UniversalTensorSquare.degreeUnionBranch62_869`, `OAI.UniversalTensorSquare.degreeUnionBranch62_886` and `OAI.UniversalTensorSquare.degreeUnionBranch62_912` of this split import it.
-- source:
--   OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 205; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Universal-Tensor-Squares-for-Symmetric-Groups-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Support/SplitUnionRowChecker.lean (declaration OAI.UniversalTensorSquare.checkRegionPrefixes_step)

import Mathlib
import Definitions.Def_OAIQ259US001

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace UniversalTensorSquare

lemma checkRegionPrefixes_step (P : List ℕ → Bool) (k n upper : ℕ)
    (regions : List PrefixRegion) (pref : List ℕ)
    (hc : ∀ a, max 1 (n/(k+1)) ≤ a → a ≤ min n upper → n ≤ (k+1)*a →
      checkRegionPrefixes P k (n-a) a
        (nextRegions a (liveRegions (k+1) n upper regions)) (a::pref) = true) :
    checkRegionPrefixes P (k+1) n upper regions pref = true := by
  sorry

end UniversalTensorSquare
end

end OAI
end
