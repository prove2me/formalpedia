-- Prove2me | Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_tr1_2_1_mem_x
-- name    : OAI.AtomicTriangular.FiniteCertificate.tr1_2_1_mem_x
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-11-12T04:29:48.60319+00:00
-- url     : https://prove2.me/theorems/dec2aa15-3955-4d2d-adc0-98159f1fd277
-- title:
--   OAI.AtomicTriangular.FiniteCertificate.tr1_2_1_mem_x: intermediate lemma from OpenAI, An atomic certificate for triangular-lattice universal optimality (result family 090)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.AtomicTriangular.sharp_gaussian_minorants_atomic`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *An atomic certificate for triangular-lattice universal optimality (result family 090)*, OpenAI Math Release, September 26, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.AtomicTriangular.FiniteCertificate.tr1_2_1_mem` of [lean/OAI/Analysis/Triangular/Taylor/TaylorRows12.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Taylor/TaylorRows12.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.AtomicTriangular.FiniteCertificate`, with `open scoped BigOperators`, `open Construction AtomicTriangular.Interval`):
--
--   ```lean
--   lemma tr1_2_1_mem_x (l : Fin 21) (r : Fin 8) : (tr1_2_1 l r).Mem (taylorRow 1 (nearNode 2) (nearDisplacement 2 1) l.val r)
--   ```
--
--   **Definitions.** The statement is written with `OAI.AtomicTriangular.Interval.RI.Mem` (definitions bundle `OAIQ257X000` of this split); `OAI.AtomicTriangular.Construction.nearDisplacement`, `OAI.AtomicTriangular.Construction.taylorRow` and `OAI.AtomicTriangular.FiniteCertificate.nearNode` (definitions bundle `OAIQ257X011` of this split); `OAI.AtomicTriangular.FiniteCertificate.tr1_2_1` (definitions bundle `OAIQ257X012` of this split).
--
--   **Used by.** The proof of `OAI.AtomicTriangular.Construction.near_positive_polynomial_x` of this split imports it.
-- source:
--   OpenAI, An atomic certificate for triangular-lattice universal optimality (result family 090), OpenAI Math Release, September 26, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/An-atomic-certificate-for-triangular-lattice-universal-optimality-September-26-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Taylor/TaylorRows12.lean (declaration OAI.AtomicTriangular.FiniteCertificate.tr1_2_1_mem)

import Mathlib
import Definitions.Def_OAIQ257X011
import Definitions.Def_OAIQ257X012

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

lemma tr1_2_1_mem_x (l : Fin 21) (r : Fin 8) : (tr1_2_1 l r).Mem (taylorRow 1 (nearNode 2) (nearDisplacement 2 1) l.val r) := by
  sorry
end AtomicTriangular.FiniteCertificate
end

end OAI
end
