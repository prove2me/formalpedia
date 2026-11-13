-- Prove2me | Theorems.Thm_OAI_AtomicTriangular_Construction_Dkernel_summable_eu
-- name    : OAI.AtomicTriangular.Construction.Dkernel_summable_eu
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-12T11:41:22.663192+00:00
-- url     : https://prove2.me/theorems/bd456fa8-2509-4658-9c9e-e79bb6e97307
-- title:
--   OAI.AtomicTriangular.Construction.Dkernel_summable_eu: intermediate lemma from OpenAI, An atomic certificate for triangular-lattice universal optimality (result family 090)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.AtomicTriangular.universal_energy_minimum`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *An atomic certificate for triangular-lattice universal optimality (result family 090)*, OpenAI Math Release, September 26, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.AtomicTriangular.Construction.Dkernel_summable` of [lean/OAI/Analysis/Triangular/Construction/BlockOperators.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Construction/BlockOperators.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.AtomicTriangular.Construction`, with `open scoped BigOperators lp`):
--
--   ```lean
--   lemma Dkernel_summable_eu (q : TailNode × Fin 2) : Summable (fun p => |Dkernel p q|)
--   ```
--
--   **Definitions.** The statement is written with `OAI.AtomicTriangular.Construction.TailNode` (definitions bundle `OAIQ334E000` of this split); `OAI.AtomicTriangular.Construction.Dkernel` (definitions bundle `OAIQ334E004` of this split).
--
--   **Used by.** The proofs of `OAI.AtomicTriangular.Construction.actualTail_full_equations_eu`, `OAI.AtomicTriangular.Construction.actual_interpolation_eu` and `OAI.AtomicTriangular.Construction.correctionTail_small_eu` and the definitions bundle `OAIQ334E006` of this split import it.
-- source:
--   OpenAI, An atomic certificate for triangular-lattice universal optimality (result family 090), OpenAI Math Release, September 26, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/An-atomic-certificate-for-triangular-lattice-universal-optimality-September-26-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Construction/BlockOperators.lean (declaration OAI.AtomicTriangular.Construction.Dkernel_summable)

import Mathlib
import Definitions.Def_OAIQ334E004

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators lp
namespace AtomicTriangular.Construction
lemma Dkernel_summable_eu (q : TailNode × Fin 2) : Summable (fun p => |Dkernel p q|) := by
  sorry
end AtomicTriangular.Construction
end

end OAI
end
