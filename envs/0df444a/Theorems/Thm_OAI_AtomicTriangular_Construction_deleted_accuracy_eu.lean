-- Prove2me | Theorems.Thm_OAI_AtomicTriangular_Construction_deleted_accuracy_eu
-- name    : OAI.AtomicTriangular.Construction.deleted_accuracy_eu
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-12T13:12:05.893935+00:00
-- url     : https://prove2.me/theorems/099bf46e-949a-4d57-a5ba-d630d59ab43a
-- title:
--   OAI.AtomicTriangular.Construction.deleted_accuracy_eu: intermediate lemma from OpenAI, An atomic certificate for triangular-lattice universal optimality (result family 090)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.AtomicTriangular.universal_energy_minimum`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *An atomic certificate for triangular-lattice universal optimality (result family 090)*, OpenAI Math Release, September 26, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.AtomicTriangular.Construction.deleted_accuracy` of [lean/OAI/Analysis/Triangular/Signs/DeletedAccuracy.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Signs/DeletedAccuracy.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.AtomicTriangular.Construction`, with `open scoped BigOperators lp`, `open Complex Matrix Set`, `open AtomicTriangular.FiniteCertificate`):
--
--   ```lean
--   lemma deleted_accuracy_eu (side : Fin 2) {z : ℝ} (hz : 0<z) (hzB : z ≤ Z) (n : Fin 7) (y : Fin 2) {τ : ℝ} (hτ : τ∈Icc 0 1) :
--       |deletedSecond (actualJ side z hz hzB) (nearNode n) (nearNode n+nearDisplacement n y*τ)-
--         finiteTaylor side (nearNode n) (nearDisplacement n y) (actualParameter z) τ|<nearError n y
--   ```
--
--   **Definitions.** The statement is written with `OAI.AtomicTriangular.Construction.Z` and `OAI.AtomicTriangular.Construction.actualParameter` (definitions bundle `OAIQ334E006` of this split); `OAI.AtomicTriangular.Construction.actualJ` (definitions bundle `OAIQ334E009` of this split); `OAI.AtomicTriangular.Construction.deletedSecond`, `OAI.AtomicTriangular.Construction.finiteTaylor`, `OAI.AtomicTriangular.Construction.nearDisplacement`, `OAI.AtomicTriangular.Construction.nearError` and `OAI.AtomicTriangular.FiniteCertificate.nearNode` (definitions bundle `OAIQ334E011` of this split).
--
--   **Used by.** The proof of `OAI.AtomicTriangular.Construction.global_signs_eu` of this split imports it.
-- source:
--   OpenAI, An atomic certificate for triangular-lattice universal optimality (result family 090), OpenAI Math Release, September 26, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/An-atomic-certificate-for-triangular-lattice-universal-optimality-September-26-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Signs/DeletedAccuracy.lean (declaration OAI.AtomicTriangular.Construction.deleted_accuracy)

import Mathlib
import Definitions.Def_OAIQ334E011

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators lp
open Complex Matrix Set
namespace AtomicTriangular.Construction
open AtomicTriangular.FiniteCertificate
lemma deleted_accuracy_eu (side : Fin 2) {z : ℝ} (hz : 0<z) (hzB : z ≤ Z) (n : Fin 7) (y : Fin 2) {τ : ℝ} (hτ : τ∈Icc 0 1) :
    |deletedSecond (actualJ side z hz hzB) (nearNode n) (nearNode n+nearDisplacement n y*τ)-
      finiteTaylor side (nearNode n) (nearDisplacement n y) (actualParameter z) τ|<nearError n y := by
  sorry
end AtomicTriangular.Construction
end

end OAI
end
