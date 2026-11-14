-- Prove2me | Theorems.Thm_OAI_NuclearUltrapower_SOS_ElementarySpectral_sum_gen_star_ca
-- name    : OAI.NuclearUltrapower.SOS.ElementarySpectral.sum_gen_star_ca
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-13T10:13:10.318205+00:00
-- url     : https://prove2.me/theorems/5d1956c4-88e6-4364-9424-66cad421cc9e
-- title:
--   OAI.NuclearUltrapower.SOS.ElementarySpectral.sum_gen_star_ca: intermediate lemma from OpenAI, A counterexample to the coarse Novikov conjecture (result family 307)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.CoarseAssembly.bounded_geometry_graph_counterexample_unconditional`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A counterexample to the coarse Novikov conjecture (result family 307)*, OpenAI Math Release, September 23, 2026, result family 307, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.NuclearUltrapower.SOS.ElementarySpectral`, with `open scoped ComplexOrder InnerProductSpace`):
--
--   ```lean
--   theorem sum_gen_star_ca (ρ : E →* unitary A) :
--       ∑ g ∈ eGenSet, star (ρ g : A) = ∑ g ∈ eGenSet, (ρ g : A)
--   ```
--
--   **Definitions.** The statement is written with `OAI.NuclearUltrapower.SOS.SL` (definitions bundle `OAIQ229C003` of this split); `OAI.NuclearUltrapower.SOS.E` (definitions bundle `OAIQ229C032` of this split); `OAI.NuclearUltrapower.SOS.eGenSet` (definitions bundle `OAIQ229C035` of this split).
--
--   **Used by.** The proofs of `OAI.CoarseAssembly.elementaryKernel_projection_ca`, `OAI.NuclearUltrapower.SOS.ElementarySpectral.deltaOp_energy_ca`, `OAI_NuclearUltrapower_SOS_ElementarySpectral_deltaOp_gap_ca` and `OAI.NuclearUltrapower.SOS.ElementarySpectral.deltaOp_nonneg_ca` of this split import it.
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

theorem sum_gen_star_ca (ρ : E →* unitary A) :
    ∑ g ∈ eGenSet, star (ρ g : A) = ∑ g ∈ eGenSet, (ρ g : A) := by
  sorry

end Algebra

end NuclearUltrapower.SOS.ElementarySpectral
end
end

end OAI
end
