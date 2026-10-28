-- Prove2me | Theorems.Thm_OAI_Kaplansky_actualAlgebra_matrix_not_properlyInfinite
-- name    : OAI.Kaplansky.actualAlgebra_matrix_not_properlyInfinite
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-26T15:40:07.797089+00:00
-- url     : https://prove2.me/theorems/d746f573-db31-4f6c-8b52-3b26d71a662b
-- title:
--   OAI.Kaplansky.actualAlgebra_matrix_not_properlyInfinite: intermediate lemma from OpenAI, A counterexample to Kaplansky's quasitrace conjecture and failure of tensor-product stable finiteness
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.KaplanskyConsequences.stable_finiteness_bundle`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A counterexample to Kaplansky's quasitrace conjecture and failure of tensor-product stable finiteness*, OpenAI Math Release, September 23, 2026, result family 294, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Kaplansky.actualAlgebra_matrix_not_properlyInfinite` of [lean/OAI/Analysis/Kaplansky/BundleTests/Obstruction.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Kaplansky/BundleTests/Obstruction.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Kaplansky`, with `open Bundle Topology`, `open ComplexGrassmann`):
--
--   ```lean
--   theorem actualAlgebra_matrix_not_properlyInfinite {m : ℕ} (hm : 0 < m) :
--       ¬ ProperlyInfinite (CStarMatrix (Fin m) (Fin m) ActualAlgebra)
--   ```
--
--   **Definitions.** The statement is written with `OAI.Kaplansky.ActualHilbert`, `OAI.Kaplansky.ActualTestFiber`, `OAI.Kaplansky.ActualTestIndex`, `OAI.Kaplansky.BoundedProduct`, `OAI.Kaplansky.SmoothTestBase`, `OAI.Kaplansky.testProjectiveDimension`, `OAI.Kaplansky.testSequenceStage` and `OAI.Kaplansky.LineStage` (definitions bundle `OAIQ15Sf000` of this split); `OAI.Kaplansky.actualHilbert_nontrivial` and `OAI.Kaplansky.boundedProductCStarAlgebra` (definitions bundle `OAIQ15Sf007` of this split); `OAI.Kaplansky.generatedAlgebra_closed` and `OAI.Kaplansky.generatedAlgebra_cstar` (definitions bundle `OAIQ15Sf008` of this split); `OAI.Kaplansky.ActualAlgebra` and `OAI.Kaplansky.actualBoundedGenerator` (definitions bundle `OAIQ15Sf010` of this split); `OAI.Kaplansky.ProperlyInfinite` (the published bundle `Def_KaplanskyStableFiniteness`).
--
--   **Used by.** The proofs of `OAI.KaplanskyConsequences.simple_stablyFinite_traceless_exists`, `OAI.KaplanskyConsequences.stable_finiteness_bundle` and `OAI.KaplanskyConsequences.trace_free_stably_finite_exists` of this split import it.
-- source:
--   OpenAI, A counterexample to Kaplansky's quasitrace conjecture and failure of tensor-product stable finiteness, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 294; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-counterexample-to-Kaplanskys-quasitrace-conjecture-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Kaplansky/BundleTests/Obstruction.lean (declaration OAI.Kaplansky.actualAlgebra_matrix_not_properlyInfinite)

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_KaplanskyStableFiniteness
import Definitions.Def_OAIQ15Sf010

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Bundle Topology
namespace Kaplansky
open ComplexGrassmann
attribute [local instance 2000] CStarAlgebra.spectralOrder CStarAlgebra.spectralOrderedRing

theorem actualAlgebra_matrix_not_properlyInfinite {m : ℕ} (hm : 0 < m) :
    ¬ ProperlyInfinite (CStarMatrix (Fin m) (Fin m) ActualAlgebra) := by
  sorry

end Kaplansky

end

end OAI
end
