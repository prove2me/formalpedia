-- Prove2me | Theorems.Thm_OAI_CubicFirstMoment_sieveExponent_four_thirds
-- name    : OAI.CubicFirstMoment.sieveExponent_four_thirds
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T03:38:21.982472+00:00
-- url     : https://prove2.me/theorems/c683f6e6-16b4-4c27-b403-0e191bcdc0a4
-- title:
--   OAI.CubicFirstMoment.sieveExponent_four_thirds: intermediate lemma from OpenAI, An unconditional first moment for cubic Gauss sums (result family 023)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.CubicFirstMoment.patterson_firstMoment`, `OAI.CubicFirstMoment.patterson_angularComparison` and `OAI.CubicFirstMoment.patterson_angularCancellation`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *An unconditional first moment for cubic Gauss sums (result family 023)*, OpenAI Math Release, September 25, 2026, result family 23, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.CubicFirstMoment.sieveExponent_four_thirds` of [lean/OAI/NumberTheory/CubicGram/SieveImprovement.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/NumberTheory/CubicGram/SieveImprovement.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.CubicFirstMoment`):
--
--   ```lean
--   theorem sieveExponent_four_thirds : SieveExponent (4/3)
--   ```
--
--   **Definitions.** The statement is written with `OAI.CubicFirstMoment.SieveExponent` (definitions bundle `OAIQ096A005` of this split).
--
--   **Used by.** The proofs of `OAI.CubicFirstMoment.LogarithmicWeightFamily.metaplectic_long_sieve`, `OAI.CubicFirstMoment.angular_scaleFirstStoppedLate_isLittleO`, `OAI.CubicFirstMoment.bounded_cubic_moment`, `OAI.CubicFirstMoment.dilated_noncube_three_sieve_bounds`, `OAI.CubicFirstMoment.first_angular_primeCoordinateError_moment`, `OAI.CubicFirstMoment.first_angular_squarefreeCoordinateError_moment`, `OAI.CubicFirstMoment.first_primeCoordinateError_moment`, `OAI.CubicFirstMoment.first_unweighted_structured_moment`, `OAI.CubicFirstMoment.gramDualTerm_dyad_rapidDecay`, `OAI.CubicFirstMoment.outer_core_block_sieve`, `OAI.CubicFirstMoment.primeGroupTail_coprime_mellin_height_power`, `OAI.CubicFirstMoment.scaleFirstStoppedLate_isLittleO`, `OAI.CubicFirstMoment.smallB_core_hybrid_sieve` and `OAI.CubicFirstMoment.small_conductor_frequency_sieve` of this split import it.
-- source:
--   OpenAI, An unconditional first moment for cubic Gauss sums (result family 023), OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 23; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/An-unconditional-first-moment-for-cubic-Gauss-sums-September-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/NumberTheory/CubicGram/SieveImprovement.lean (declaration OAI.CubicFirstMoment.sieveExponent_four_thirds)

import Mathlib
import Definitions.Def_OAIQ096A005

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

theorem sieveExponent_four_thirds : SieveExponent (4/3) := by
  sorry

end CubicFirstMoment
end
end

end OAI
end
