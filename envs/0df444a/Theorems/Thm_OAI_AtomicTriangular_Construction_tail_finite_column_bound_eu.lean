-- Prove2me | Theorems.Thm_OAI_AtomicTriangular_Construction_tail_finite_column_bound_eu
-- name    : OAI.AtomicTriangular.Construction.tail_finite_column_bound_eu
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-12T11:43:12.572818+00:00
-- url     : https://prove2.me/theorems/7fa488e5-befa-4b81-a7cd-0db3c50fe18e
-- title:
--   OAI.AtomicTriangular.Construction.tail_finite_column_bound_eu: intermediate lemma from OpenAI, An atomic certificate for triangular-lattice universal optimality (result family 090)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.AtomicTriangular.universal_energy_minimum`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *An atomic certificate for triangular-lattice universal optimality (result family 090)*, OpenAI Math Release, September 26, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.AtomicTriangular.Construction.tail_finite_column_bound` of [lean/OAI/Analysis/Triangular/Envelope/KernelBounds.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Envelope/KernelBounds.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.AtomicTriangular.Construction`, with `open scoped BigOperators`):
--
--   ```lean
--   lemma tail_finite_column_bound_eu (c : Fin 22) :
--       (∑' p : TailNode × Fin 2, |jet H h p.1.val.val p.2 (finiteColumn ⟨c.val,by omega⟩)|) < 7/10^15
--   ```
--
--   **Definitions.** The statement is written with `OAI.AtomicTriangular.Construction.FiniteNodes`, `OAI.AtomicTriangular.Construction.H`, `OAI.AtomicTriangular.Construction.Node`, `OAI.AtomicTriangular.Construction.TailNode`, `OAI.AtomicTriangular.Construction.finiteColumn`, `OAI.AtomicTriangular.Construction.h` and `OAI.AtomicTriangular.Construction.residues` (definitions bundle `OAIQ334E000` of this split); `OAI.AtomicTriangular.Construction.jet` (definitions bundle `OAIQ334E002` of this split).
--
--   **Used by.** The proofs of `OAI.AtomicTriangular.Construction.Ckernel_bound_eu`, `OAI.AtomicTriangular.Construction.actualTail_full_equations_eu`, `OAI.AtomicTriangular.Construction.actual_interpolation_eu` and `OAI.AtomicTriangular.Construction.approximationTailResidual_norm_eu` and the definitions bundle `OAIQ334E006` of this split import it.
-- source:
--   OpenAI, An atomic certificate for triangular-lattice universal optimality (result family 090), OpenAI Math Release, September 26, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/An-atomic-certificate-for-triangular-lattice-universal-optimality-September-26-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Envelope/KernelBounds.lean (declaration OAI.AtomicTriangular.Construction.tail_finite_column_bound)

import Mathlib
import Definitions.Def_OAIQ334E002

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.Construction
lemma tail_finite_column_bound_eu (c : Fin 22) :
    (∑' p : TailNode × Fin 2, |jet H h p.1.val.val p.2 (finiteColumn ⟨c.val,by omega⟩)|) < 7/10^15 := by
  sorry
end AtomicTriangular.Construction
end

end OAI
end
