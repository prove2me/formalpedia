-- Prove2me | Theorems.Thm_OAI_JointDickman_primeProductMertensInput_jd
-- name    : OAI.JointDickman.primeProductMertensInput_jd
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-31T20:29:39.182216+00:00
-- url     : https://prove2.me/theorems/0b52b8b7-aaf1-494a-ad34-0dad1ca8b3de
-- title:
--   OAI.JointDickman.primeProductMertensInput_jd: intermediate lemma from OpenAI, The joint Dickman law for consecutive integers
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.JointDickmanPaper.joint_law`, `OAI.JointDickmanPaper.increasing_order` and `OAI.JointDickmanPaper.decreasing_order`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The joint Dickman law for consecutive integers*, OpenAI Math Release, September 24, 2026, result family 12, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.JointDickman.primeProductMertensInput` of [lean/OAI/NumberTheory/JointDickman/Arithmetic/MertensDischarge.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/NumberTheory/JointDickman/Arithmetic/MertensDischarge.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.JointDickman`, with `open Finset Filter`, `open scoped Topology`):
--
--   ```lean
--   theorem primeProductMertensInput_jd : PublishedInputs.PrimeProductMertensInput
--   ```
--
--   **Definitions.** The statement is written with `OAI.JointDickman.PublishedInputs.PrimeProductMertensInput` (definitions bundle `OAIQ083J001` of this split).
--
--   **Used by.** The proofs of `OAI.JointDickman.jointDickmanLaw_unconditional_jd` and `OAI.JointDickman.ramare_product_sparse_integral_jd` of this split import it.
-- source:
--   OpenAI, The joint Dickman law for consecutive integers, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 12; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-joint-Dickman-law-for-consecutive-integers-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/NumberTheory/JointDickman/Arithmetic/MertensDischarge.lean (declaration OAI.JointDickman.primeProductMertensInput)

import Mathlib
import Definitions.Def_OAIQ083J001

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace JointDickman
open Finset Filter
open scoped Topology

theorem primeProductMertensInput_jd : PublishedInputs.PrimeProductMertensInput := by
  sorry

end JointDickman

end OAI
end
