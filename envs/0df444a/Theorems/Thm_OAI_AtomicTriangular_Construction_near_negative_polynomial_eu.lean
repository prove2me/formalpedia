-- Prove2me | Theorems.Thm_OAI_AtomicTriangular_Construction_near_negative_polynomial_eu
-- name    : OAI.AtomicTriangular.Construction.near_negative_polynomial_eu
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-12T13:12:29.623437+00:00
-- url     : https://prove2.me/theorems/210d03d7-04e1-45ab-a2c8-f89473ab74db
-- title:
--   OAI.AtomicTriangular.Construction.near_negative_polynomial_eu: intermediate lemma from OpenAI, An atomic certificate for triangular-lattice universal optimality (result family 090)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.AtomicTriangular.universal_energy_minimum`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *An atomic certificate for triangular-lattice universal optimality (result family 090)*, OpenAI Math Release, September 26, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.AtomicTriangular.Construction.near_negative_polynomial` of [lean/OAI/Analysis/Triangular/Signs/OrdinaryComparison.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Signs/OrdinaryComparison.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.AtomicTriangular.Construction`, with `open scoped BigOperators`, `open Set`, `open AtomicTriangular.FiniteCertificate`):
--
--   ```lean
--   lemma near_negative_polynomial_eu (e : Fin 8 → ℝ) (he : ParameterPolytope e)
--       (n : Fin 7) (y : Fin 2) (hne : ¬(n=0 ∧ y=1)) {τ : ℝ} (hτ : τ∈Icc 0 1) :
--       nearError n y < (∑ r : Fin 8,ordinaryOffset n r*e r)-
--         finiteTaylor 0 (nearNode n) (nearDisplacement n y) e τ
--   ```
--
--   **Definitions.** The statement is written with `OAI.AtomicTriangular.Construction.ParameterPolytope`, `OAI.AtomicTriangular.Construction.finiteTaylor`, `OAI.AtomicTriangular.Construction.nearDisplacement`, `OAI.AtomicTriangular.Construction.nearError`, `OAI.AtomicTriangular.Construction.ordinaryOffset` and `OAI.AtomicTriangular.FiniteCertificate.nearNode` (definitions bundle `OAIQ334E011` of this split).
--
--   **Used by.** The proof of `OAI.AtomicTriangular.Construction.global_signs_eu` of this split imports it.
-- source:
--   OpenAI, An atomic certificate for triangular-lattice universal optimality (result family 090), OpenAI Math Release, September 26, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/An-atomic-certificate-for-triangular-lattice-universal-optimality-September-26-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Signs/OrdinaryComparison.lean (declaration OAI.AtomicTriangular.Construction.near_negative_polynomial)

import Mathlib
import Definitions.Def_OAIQ334E011

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
lemma near_negative_polynomial_eu (e : Fin 8 → ℝ) (he : ParameterPolytope e)
    (n : Fin 7) (y : Fin 2) (hne : ¬(n=0 ∧ y=1)) {τ : ℝ} (hτ : τ∈Icc 0 1) :
    nearError n y < (∑ r : Fin 8,ordinaryOffset n r*e r)-
      finiteTaylor 0 (nearNode n) (nearDisplacement n y) e τ := by
  sorry
end AtomicTriangular.Construction
end

end OAI
end
