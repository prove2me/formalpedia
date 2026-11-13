-- Prove2me | Theorems.Thm_OAI_AtomicTriangular_Construction_exceptional_rational_comparison_tg
-- name    : OAI.AtomicTriangular.Construction.exceptional_rational_comparison_tg
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-12T07:26:45.449966+00:00
-- url     : https://prove2.me/theorems/b792905c-0485-4e1e-b73e-3ec5fa475ead
-- title:
--   OAI.AtomicTriangular.Construction.exceptional_rational_comparison_tg: intermediate lemma from OpenAI, An atomic certificate for triangular-lattice universal optimality (result family 090)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.AtomicTriangular.sharp_gaussian_minorants_with_construction`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *An atomic certificate for triangular-lattice universal optimality (result family 090)*, OpenAI Math Release, September 26, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.AtomicTriangular.Construction.exceptional_rational_comparison` of [lean/OAI/Analysis/Triangular/Signs/ExceptionalComparison.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Signs/ExceptionalComparison.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.AtomicTriangular.Construction`, with `open scoped BigOperators`, `open Set`, `open AtomicTriangular.FiniteCertificate`):
--
--   ```lean
--   lemma exceptional_rational_comparison_tg (e : Fin 8 → ℝ) (he : ParameterPolytope e)
--       {v : ℝ} (hv : v∈Icc 0 1) (hz : 0<e 0) (hzB : e 0 ≤ Z) :
--       finiteTaylor 0 1 1 e v+3/1000 ≤ Q 1*((3*(e 0)+v)/(6*(e 0)^2+4*(e 0)*v+v^2))
--   ```
--
--   **Definitions.** The statement is written with `OAI.AtomicTriangular.Construction.ParameterPolytope` and `OAI.AtomicTriangular.Construction.Z` (definitions bundle `OAIQ262T001` of this split); `OAI.AtomicTriangular.Construction.finiteTaylor` (definitions bundle `OAIQ262T097` of this split); `OAI.AtomicTriangular.Construction.Q` (the published bundle `Def_TriangularGaussian`).
--
--   **Used by.** The proof of `OAI.AtomicTriangular.Construction.global_signs_tg` of this split imports it.
-- source:
--   OpenAI, An atomic certificate for triangular-lattice universal optimality (result family 090), OpenAI Math Release, September 26, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/An-atomic-certificate-for-triangular-lattice-universal-optimality-September-26-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Signs/ExceptionalComparison.lean (declaration OAI.AtomicTriangular.Construction.exceptional_rational_comparison)

import Mathlib
import Definitions.Def_TriangularGaussian
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
lemma exceptional_rational_comparison_tg (e : Fin 8 → ℝ) (he : ParameterPolytope e)
    {v : ℝ} (hv : v∈Icc 0 1) (hz : 0<e 0) (hzB : e 0 ≤ Z) :
    finiteTaylor 0 1 1 e v+3/1000 ≤ Q 1*((3*(e 0)+v)/(6*(e 0)^2+4*(e 0)*v+v^2)) := by
  sorry
end AtomicTriangular.Construction
end

end OAI
end
