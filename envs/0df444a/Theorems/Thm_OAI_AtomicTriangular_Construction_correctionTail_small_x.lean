-- Prove2me | Theorems.Thm_OAI_AtomicTriangular_Construction_correctionTail_small_x
-- name    : OAI.AtomicTriangular.Construction.correctionTail_small_x
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-12T04:16:45.03407+00:00
-- url     : https://prove2.me/theorems/d6398276-977e-49fc-b699-9d851edfb5fd
-- title:
--   OAI.AtomicTriangular.Construction.correctionTail_small_x: intermediate lemma from OpenAI, An atomic certificate for triangular-lattice universal optimality (result family 090)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.AtomicTriangular.sharp_gaussian_minorants_atomic`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *An atomic certificate for triangular-lattice universal optimality (result family 090)*, OpenAI Math Release, September 26, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.AtomicTriangular.Construction.correctionTail_small` of [lean/OAI/Analysis/Triangular/Construction/ConcreteSchur.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Construction/ConcreteSchur.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.AtomicTriangular.Construction`, with `open scoped BigOperators lp`, `open AtomicTriangular.Schur`):
--
--   ```lean
--   lemma correctionTail_small_x (e : Fin 2) (r : FiniteCoefficients) (s : TailCoefficients)
--       (hr : ‖r‖≤finiteResidualBound) (hs : ‖s‖≤tailResidualBound e) :
--       ‖correctionTail e r s‖ ≤ tailErrorBound e
--   ```
--
--   **Definitions.** The statement is written with `OAI.AtomicTriangular.Construction.FiniteCoefficients`, `OAI.AtomicTriangular.Construction.TailCoefficients` and `OAI.AtomicTriangular.Construction.correctionTail` (definitions bundle `OAIQ257X006` of this split); `OAI.AtomicTriangular.Construction.finiteResidualBound`, `OAI.AtomicTriangular.Construction.tailErrorBound` and `OAI.AtomicTriangular.Construction.tailResidualBound` (definitions bundle `OAIQ257X011` of this split); `OAI.AtomicTriangular.Construction.TailNode` (the published bundle `Def_AtomicGaussian`).
--
--   **Used by.** The proofs of `OAI.AtomicTriangular.Construction.actualTail_norm_x` and `OAI.AtomicTriangular.Construction.correctionFinite_small_x` of this split import it.
-- source:
--   OpenAI, An atomic certificate for triangular-lattice universal optimality (result family 090), OpenAI Math Release, September 26, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/An-atomic-certificate-for-triangular-lattice-universal-optimality-September-26-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Construction/ConcreteSchur.lean (declaration OAI.AtomicTriangular.Construction.correctionTail_small)

import Mathlib
import Definitions.Def_AtomicGaussian
import Definitions.Def_OAIQ257X011

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators lp
namespace AtomicTriangular.Construction
open AtomicTriangular.Schur

lemma correctionTail_small_x (e : Fin 2) (r : FiniteCoefficients) (s : TailCoefficients)
    (hr : ‖r‖≤finiteResidualBound) (hs : ‖s‖≤tailResidualBound e) :
    ‖correctionTail e r s‖ ≤ tailErrorBound e := by
  sorry
end AtomicTriangular.Construction
end

end OAI
end
