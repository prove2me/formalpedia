-- Prove2me | Theorems.Thm_OAI_NuclearUltrapower_SOS_goodWord_mul_ca
-- name    : OAI.NuclearUltrapower.SOS.goodWord_mul_ca
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-13T10:15:42.915344+00:00
-- url     : https://prove2.me/theorems/1955c7f6-8c86-4442-9689-c72bc3e4a789
-- title:
--   OAI.NuclearUltrapower.SOS.goodWord_mul_ca: intermediate lemma from OpenAI, A counterexample to the coarse Novikov conjecture (result family 307)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.CoarseAssembly.bounded_geometry_graph_counterexample_unconditional`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A counterexample to the coarse Novikov conjecture (result family 307)*, OpenAI Math Release, September 23, 2026, result family 307, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.NuclearUltrapower.SOS`):
--
--   ```lean
--   theorem goodWord_mul_ca {n k : ℕ} {a b : Mat3} (ha : GoodWord n a) (hb : GoodWord k b) :
--       GoodWord (n+k) (matMul a b)
--   ```
--
--   **Definitions.** The statement is written with `OAI.NuclearUltrapower.SOS.Mat3` (definitions bundle `OAIQ229C003` of this split); `OAI.NuclearUltrapower.SOS.matMul` (definitions bundle `OAIQ229C015` of this split); `OAI.NuclearUltrapower.SOS.GoodWord` (definitions bundle `OAIQ229C035` of this split).
--
--   **Used by.** The proofs of `OAI_CoarseAssembly_provedKazhdanInput_ca`, `OAI.CoarseAssembly.publishedKazhdanInput_of_elementaryReduction_ca`, `OAI_NuclearUltrapower_SOS_ElementarySpectral_deltaOp_gap_ca`, `OAI.NuclearUltrapower.SOS.ElementarySpectral.value_mul_ca` and `OAI.NuclearUltrapower.SOS.basis_good_ca` of this split import it.
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
namespace NuclearUltrapower.SOS

theorem goodWord_mul_ca {n k : ℕ} {a b : Mat3} (ha : GoodWord n a) (hb : GoodWord k b) :
    GoodWord (n+k) (matMul a b) := by
  sorry

end NuclearUltrapower.SOS
end
end

end OAI
end
