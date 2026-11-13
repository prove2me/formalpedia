-- Prove2me | Theorems.Thm_OAI_AtomicTriangular_Construction_finiteTaylor_error_eu
-- name    : OAI.AtomicTriangular.Construction.finiteTaylor_error_eu
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-12T13:12:19.408726+00:00
-- url     : https://prove2.me/theorems/a8208bb0-3879-4944-8d48-51be33297c1f
-- title:
--   OAI.AtomicTriangular.Construction.finiteTaylor_error_eu: intermediate lemma from OpenAI, An atomic certificate for triangular-lattice universal optimality (result family 090)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.AtomicTriangular.universal_energy_minimum`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *An atomic certificate for triangular-lattice universal optimality (result family 090)*, OpenAI Math Release, September 26, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.AtomicTriangular.Construction.finiteTaylor_error` of [lean/OAI/Analysis/Triangular/Taylor/FiniteTaylorError.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Taylor/FiniteTaylorError.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.AtomicTriangular.Construction`, with `open scoped BigOperators lp`, `open Complex Matrix`, `open AtomicTriangular.FiniteCertificate`):
--
--   ```lean
--   lemma finiteTaylor_error_eu (side : Fin 2) {z : ℝ} (hz : 0<z) (hzB : z≤Z) (n : Fin 7) {y τ : ℝ}
--       (hv : |y*τ|≤nearRadius n) :
--       |deletedSecond (finiteJ side (actualParameter z)) (nearNode n) (nearNode n+y*τ)-finiteTaylor side (nearNode n) y (actualParameter z) τ| <
--         (if n.val=0 then (161/100000:ℝ) else 75/10000000)
--   ```
--
--   **Definitions.** The statement is written with `OAI.AtomicTriangular.Construction.Z` and `OAI.AtomicTriangular.Construction.actualParameter` (definitions bundle `OAIQ334E006` of this split); `OAI.AtomicTriangular.Construction.deletedSecond`, `OAI.AtomicTriangular.Construction.finiteJ`, `OAI.AtomicTriangular.Construction.finiteTaylor`, `OAI.AtomicTriangular.Construction.nearRadius` and `OAI.AtomicTriangular.FiniteCertificate.nearNode` (definitions bundle `OAIQ334E011` of this split).
--
--   **Used by.** The proof of `OAI.AtomicTriangular.Construction.deleted_accuracy_eu` of this split imports it.
-- source:
--   OpenAI, An atomic certificate for triangular-lattice universal optimality (result family 090), OpenAI Math Release, September 26, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/An-atomic-certificate-for-triangular-lattice-universal-optimality-September-26-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Taylor/FiniteTaylorError.lean (declaration OAI.AtomicTriangular.Construction.finiteTaylor_error)

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
open Complex Matrix
namespace AtomicTriangular.Construction
open AtomicTriangular.FiniteCertificate
lemma finiteTaylor_error_eu (side : Fin 2) {z : ℝ} (hz : 0<z) (hzB : z≤Z) (n : Fin 7) {y τ : ℝ}
    (hv : |y*τ|≤nearRadius n) :
    |deletedSecond (finiteJ side (actualParameter z)) (nearNode n) (nearNode n+y*τ)-finiteTaylor side (nearNode n) y (actualParameter z) τ| <
      (if n.val=0 then (161/100000:ℝ) else 75/10000000) := by
  sorry
end AtomicTriangular.Construction
end

end OAI
end
