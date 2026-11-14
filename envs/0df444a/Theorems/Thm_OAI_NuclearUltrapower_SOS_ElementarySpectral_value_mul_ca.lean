-- Prove2me | Theorems.Thm_OAI_NuclearUltrapower_SOS_ElementarySpectral_value_mul_ca
-- name    : OAI.NuclearUltrapower.SOS.ElementarySpectral.value_mul_ca
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-13T10:31:44.81449+00:00
-- url     : https://prove2.me/theorems/0494404a-763f-441f-89a1-86425210a6b4
-- title:
--   OAI.NuclearUltrapower.SOS.ElementarySpectral.value_mul_ca: intermediate lemma from OpenAI, A counterexample to the coarse Novikov conjecture (result family 307)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.CoarseAssembly.bounded_geometry_graph_counterexample_unconditional`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A counterexample to the coarse Novikov conjecture (result family 307)*, OpenAI Math Release, September 23, 2026, result family 307, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.NuclearUltrapower.SOS.ElementarySpectral`, with `open scoped ComplexOrder InnerProductSpace`):
--
--   ```lean
--   theorem value_mul_ca (ρ : E →* unitary A) {n k : ℕ} (a b : Mat3)
--       (ha : GoodWord n a) (hb : GoodWord k b) :
--       value ρ (matMul a b) = value ρ a * value ρ b
--   ```
--
--   **Definitions.** The statement is written with `OAI.NuclearUltrapower.SOS.Mat3` and `OAI.NuclearUltrapower.SOS.SL` (definitions bundle `OAIQ229C003` of this split); `OAI.NuclearUltrapower.SOS.matMul` (definitions bundle `OAIQ229C015` of this split); `OAI.NuclearUltrapower.SOS.E` (definitions bundle `OAIQ229C032` of this split); `OAI.NuclearUltrapower.SOS.GoodWord` and `OAI.NuclearUltrapower.SOS.ElementarySpectral.value` (definitions bundle `OAIQ229C035` of this split).
--
--   **Used by.** The proofs of `OAI.NuclearUltrapower.SOS.ElementarySpectral.deltaOp_certificate_ca` and `OAI_NuclearUltrapower_SOS_ElementarySpectral_deltaOp_gap_ca` of this split import it.
-- source:
--   OpenAI, A counterexample to the coarse Novikov conjecture (result family 307), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 307; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/CoarseAssembly.lean; Apache License 2.0)

import Mathlib
import Definitions.Def_OAIQ229C035

section

attribute [-instance] _root_.OAI.CoarseAssembly.baseUnionDecidableEq _root_.OAI.CoarseAssembly.instFintypeFiberVertex _root_.OAI.CoarseAssembly.vertexUnionDecidableEq _root_.OAI.NuclearUltrapower.strongDualInner
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped ComplexOrder InnerProductSpace
namespace NuclearUltrapower.SOS.ElementarySpectral

section Algebra
variable {A : Type*} [CStarAlgebra A]

theorem value_mul_ca (ρ : E →* unitary A) {n k : ℕ} (a b : Mat3)
    (ha : GoodWord n a) (hb : GoodWord k b) :
    value ρ (matMul a b) = value ρ a * value ρ b := by
  sorry

end Algebra

end NuclearUltrapower.SOS.ElementarySpectral
end
end

end OAI
end
