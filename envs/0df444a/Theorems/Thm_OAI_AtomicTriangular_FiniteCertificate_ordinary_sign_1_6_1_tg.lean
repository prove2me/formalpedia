-- Prove2me | Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_ordinary_sign_1_6_1_tg
-- name    : OAI.AtomicTriangular.FiniteCertificate.ordinary_sign_1_6_1_tg
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-12T07:27:50.527289+00:00
-- url     : https://prove2.me/theorems/f2b6b449-b44b-4d95-9e08-d84764b55e9c
-- title:
--   OAI.AtomicTriangular.FiniteCertificate.ordinary_sign_1_6_1_tg: intermediate lemma from OpenAI, An atomic certificate for triangular-lattice universal optimality (result family 090)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.AtomicTriangular.sharp_gaussian_minorants_with_construction`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *An atomic certificate for triangular-lattice universal optimality (result family 090)*, OpenAI Math Release, September 26, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.AtomicTriangular.FiniteCertificate.ordinary_sign_1_6_1` of [lean/OAI/Analysis/Triangular/Signs/Signs16.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Signs/Signs16.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.AtomicTriangular.FiniteCertificate`, with `open scoped BigOperators`, `open Construction AtomicTriangular.Interval`):
--
--   ```lean
--   lemma ordinary_sign_1_6_1_tg (e : Fin 8 → ℝ) (he : ParameterPolytope e)
--       {τ : ℝ} (hτ : τ ∈ Set.Icc 0 1) :
--       (2000/1000000:ℝ) < ordinarySignValue 1 6 1 e τ
--   ```
--
--   **Definitions.** The statement is written with `OAI.AtomicTriangular.Construction.ParameterPolytope` (definitions bundle `OAIQ262T001` of this split); `OAI.AtomicTriangular.Construction.ordinarySignValue` (definitions bundle `OAIQ262T148` of this split).
--
--   **Used by.** The proof of `OAI.AtomicTriangular.Construction.near_positive_polynomial_tg` of this split imports it.
-- source:
--   OpenAI, An atomic certificate for triangular-lattice universal optimality (result family 090), OpenAI Math Release, September 26, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/An-atomic-certificate-for-triangular-lattice-universal-optimality-September-26-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Signs/Signs16.lean (declaration OAI.AtomicTriangular.FiniteCertificate.ordinary_sign_1_6_1)

import Mathlib
import Definitions.Def_OAIQ262T148

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval
lemma ordinary_sign_1_6_1_tg (e : Fin 8 → ℝ) (he : ParameterPolytope e)
    {τ : ℝ} (hτ : τ ∈ Set.Icc 0 1) :
    (2000/1000000:ℝ) < ordinarySignValue 1 6 1 e τ := by
  sorry
end AtomicTriangular.FiniteCertificate
end

end OAI
end
