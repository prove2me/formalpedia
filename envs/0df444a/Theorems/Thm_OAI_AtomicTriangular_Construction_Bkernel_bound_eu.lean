-- Prove2me | Theorems.Thm_OAI_AtomicTriangular_Construction_Bkernel_bound_eu
-- name    : OAI.AtomicTriangular.Construction.Bkernel_bound_eu
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-12T11:38:40.132033+00:00
-- url     : https://prove2.me/theorems/4b771d6f-04d6-46e9-8ea6-dd972f44d165
-- title:
--   OAI.AtomicTriangular.Construction.Bkernel_bound_eu: intermediate lemma from OpenAI, An atomic certificate for triangular-lattice universal optimality (result family 090)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.AtomicTriangular.universal_energy_minimum`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *An atomic certificate for triangular-lattice universal optimality (result family 090)*, OpenAI Math Release, September 26, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.AtomicTriangular.Construction.Bkernel_bound` of [lean/OAI/Analysis/Triangular/Construction/BlockOperators.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Construction/BlockOperators.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.AtomicTriangular.Construction`, with `open scoped BigOperators lp`):
--
--   ```lean
--   lemma Bkernel_bound_eu (p : TailNode × Fin 2) : (∑' i, |Bkernel i p|) ≤ 335
--   ```
--
--   **Definitions.** The statement is written with `OAI.AtomicTriangular.Construction.Bkernel` and `OAI.AtomicTriangular.Construction.TailNode` (definitions bundle `OAIQ334E000` of this split).
--
--   **Used by.** The proofs of `OAI.AtomicTriangular.Construction.actualTail_full_equations_eu`, `OAI.AtomicTriangular.Construction.actual_interpolation_eu`, `OAI.AtomicTriangular.Construction.correctionFinite_small_eu` and `OAI.AtomicTriangular.Construction.correctionTail_small_eu` and the definitions bundle `OAIQ334E006` of this split import it.
-- source:
--   OpenAI, An atomic certificate for triangular-lattice universal optimality (result family 090), OpenAI Math Release, September 26, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/An-atomic-certificate-for-triangular-lattice-universal-optimality-September-26-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Construction/BlockOperators.lean (declaration OAI.AtomicTriangular.Construction.Bkernel_bound)

import Mathlib
import Definitions.Def_OAIQ334E000

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators lp
namespace AtomicTriangular.Construction
lemma Bkernel_bound_eu (p : TailNode × Fin 2) : (∑' i, |Bkernel i p|) ≤ 335 := by
  sorry
end AtomicTriangular.Construction
end

end OAI
end
