-- Prove2me | Theorems.Thm_OAI_AtomicTriangular_Construction_tail_atom_column_bounds_x
-- name    : OAI.AtomicTriangular.Construction.tail_atom_column_bounds_x
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-12T03:34:21.542883+00:00
-- url     : https://prove2.me/theorems/7b6e4e74-d17c-4f33-ba42-6a484edfd37c
-- title:
--   OAI.AtomicTriangular.Construction.tail_atom_column_bounds_x: intermediate lemma from OpenAI, An atomic certificate for triangular-lattice universal optimality (result family 090)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.AtomicTriangular.sharp_gaussian_minorants_atomic`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *An atomic certificate for triangular-lattice universal optimality (result family 090)*, OpenAI Math Release, September 26, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.AtomicTriangular.Construction.tail_atom_column_bounds` of [lean/OAI/Analysis/Triangular/Envelope/KernelBounds.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Envelope/KernelBounds.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.AtomicTriangular.Construction`, with `open scoped BigOperators`):
--
--   ```lean
--   lemma tail_atom_column_bounds_x (q v : Fin 2) (S : Fin 31 → ℂ) :
--       Summable (fun p : TailNode × Fin 2 => |jet (damping q) (damping v) p.1.val.val p.2 S|) ∧
--       (∑' p : TailNode × Fin 2, |jet (damping q) (damping v) p.1.val.val p.2 S|)  ≤
--         ∑ j : Fin 31, tailEnvelopeSum q v j*‖S j‖
--   ```
--
--   **Definitions.** The statement is written with `OAI.AtomicTriangular.Construction.damping` (definitions bundle `OAIQ257X000` of this split); `OAI.AtomicTriangular.Construction.tailEnvelopeSum` (definitions bundle `OAIQ257X003` of this split); `OAI.AtomicTriangular.Construction.FiniteNodes`, `OAI.AtomicTriangular.Construction.Node`, `OAI.AtomicTriangular.Construction.TailNode`, `OAI.AtomicTriangular.Construction.jet` and `OAI.AtomicTriangular.Construction.residues` (the published bundle `Def_AtomicGaussian`).
--
--   **Used by.** The proofs of `OAI.AtomicTriangular.Construction.Ckernel_summable_x`, `OAI.AtomicTriangular.Construction.tailFixedColumn_norm_constant_x` and `OAI.AtomicTriangular.Construction.tail_finite_column_bound_x` and the definitions bundle `OAIQ257X006` of this split import it.
-- source:
--   OpenAI, An atomic certificate for triangular-lattice universal optimality (result family 090), OpenAI Math Release, September 26, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/An-atomic-certificate-for-triangular-lattice-universal-optimality-September-26-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Envelope/KernelBounds.lean (declaration OAI.AtomicTriangular.Construction.tail_atom_column_bounds)

import Mathlib
import Definitions.Def_AtomicGaussian
import Definitions.Def_OAIQ257X003

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.Construction
lemma tail_atom_column_bounds_x (q v : Fin 2) (S : Fin 31 → ℂ) :
    Summable (fun p : TailNode × Fin 2 => |jet (damping q) (damping v) p.1.val.val p.2 S|) ∧
    (∑' p : TailNode × Fin 2, |jet (damping q) (damping v) p.1.val.val p.2 S|)  ≤
      ∑ j : Fin 31, tailEnvelopeSum q v j*‖S j‖ := by
  sorry
end AtomicTriangular.Construction
end

end OAI
end
