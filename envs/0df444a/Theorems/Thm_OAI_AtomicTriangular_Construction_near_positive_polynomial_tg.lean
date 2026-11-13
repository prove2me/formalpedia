-- Prove2me | Theorems.Thm_OAI_AtomicTriangular_Construction_near_positive_polynomial_tg
-- name    : OAI.AtomicTriangular.Construction.near_positive_polynomial_tg
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-12T07:28:37.579785+00:00
-- url     : https://prove2.me/theorems/27524e29-3529-4de4-b968-95a32f452e09
-- title:
--   OAI.AtomicTriangular.Construction.near_positive_polynomial_tg: intermediate lemma from OpenAI, An atomic certificate for triangular-lattice universal optimality (result family 090)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.AtomicTriangular.sharp_gaussian_minorants_with_construction`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *An atomic certificate for triangular-lattice universal optimality (result family 090)*, OpenAI Math Release, September 26, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.AtomicTriangular.Construction.near_positive_polynomial` of [lean/OAI/Analysis/Triangular/Signs/OrdinaryComparison.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Signs/OrdinaryComparison.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.AtomicTriangular.Construction`, with `open scoped BigOperators`, `open Set`, `open AtomicTriangular.FiniteCertificate`):
--
--   ```lean
--   lemma near_positive_polynomial_tg (e : Fin 8 → ℝ) (he : ParameterPolytope e)
--       (n : Fin 7) (y : Fin 2) {τ : ℝ} (hτ : τ∈Icc 0 1) :
--       nearError n y < finiteTaylor 1 (nearNode n) (nearDisplacement n y) e τ
--   ```
--
--   **Definitions.** The statement is written with `OAI.AtomicTriangular.Construction.ParameterPolytope` (definitions bundle `OAIQ262T001` of this split); `OAI.AtomicTriangular.Construction.nearDisplacement`, `OAI.AtomicTriangular.Construction.nearError` and `OAI.AtomicTriangular.FiniteCertificate.nearNode` (definitions bundle `OAIQ262T003` of this split); `OAI.AtomicTriangular.Construction.finiteTaylor` (definitions bundle `OAIQ262T097` of this split).
--
--   **Used by.** The proof of `OAI.AtomicTriangular.Construction.global_signs_tg` of this split imports it.
-- source:
--   OpenAI, An atomic certificate for triangular-lattice universal optimality (result family 090), OpenAI Math Release, September 26, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/An-atomic-certificate-for-triangular-lattice-universal-optimality-September-26-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Signs/OrdinaryComparison.lean (declaration OAI.AtomicTriangular.Construction.near_positive_polynomial)

import Mathlib
import Definitions.Def_OAIQ262T097

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
open Set
namespace AtomicTriangular.Construction
open AtomicTriangular.FiniteCertificate
lemma near_positive_polynomial_tg (e : Fin 8 → ℝ) (he : ParameterPolytope e)
    (n : Fin 7) (y : Fin 2) {τ : ℝ} (hτ : τ∈Icc 0 1) :
    nearError n y < finiteTaylor 1 (nearNode n) (nearDisplacement n y) e τ := by
  sorry
end AtomicTriangular.Construction
end

end OAI
end
