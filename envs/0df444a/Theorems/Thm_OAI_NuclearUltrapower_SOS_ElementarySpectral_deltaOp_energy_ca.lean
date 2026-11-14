-- Prove2me | Theorems.Thm_OAI_NuclearUltrapower_SOS_ElementarySpectral_deltaOp_energy_ca
-- name    : OAI.NuclearUltrapower.SOS.ElementarySpectral.deltaOp_energy_ca
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-13T10:20:40.050648+00:00
-- url     : https://prove2.me/theorems/743dd93e-3013-48d5-9b20-414ae3949b1a
-- title:
--   OAI.NuclearUltrapower.SOS.ElementarySpectral.deltaOp_energy_ca: intermediate lemma from OpenAI, A counterexample to the coarse Novikov conjecture (result family 307)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.CoarseAssembly.bounded_geometry_graph_counterexample_unconditional`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A counterexample to the coarse Novikov conjecture (result family 307)*, OpenAI Math Release, September 23, 2026, result family 307, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.NuclearUltrapower.SOS.ElementarySpectral`, with `open scoped InnerProductSpace ComplexOrder`):
--
--   ```lean
--   theorem deltaOp_energy_ca (ρ : E →* (H ≃ₗᵢ[ℂ] H)) (x : H) :
--       (inner ℂ x (deltaOp ρ x)).re = SOSEnergy.energy eGenSet ρ x / 2
--   ```
--
--   **Definitions.** The statement is written with `OAI.NuclearUltrapower.SOS.SL` (definitions bundle `OAIQ229C003` of this split); `OAI.NuclearUltrapower.SOSEnergy.energy` (definitions bundle `OAIQ229C004` of this split); `OAI.NuclearUltrapower.SOS.E` (definitions bundle `OAIQ229C032` of this split); `OAI.NuclearUltrapower.SOS.eGenSet` (definitions bundle `OAIQ229C035` of this split); `OAI.NuclearUltrapower.SOS.ElementarySpectral.deltaOp` (definitions bundle `OAIQ229C037` of this split).
--
--   **Used by.** The proofs of `OAI_CoarseAssembly_provedKazhdanInput_ca` and `OAI.CoarseAssembly.publishedKazhdanInput_of_elementaryReduction_ca` of this split import it.
-- source:
--   OpenAI, A counterexample to the coarse Novikov conjecture (result family 307), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 307; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/CoarseAssembly.lean; Apache License 2.0)

import Mathlib
import Definitions.Def_OAIQ229C037

section

attribute [-instance] _root_.OAI.CoarseAssembly.baseUnionDecidableEq _root_.OAI.CoarseAssembly.instFintypeFiberVertex _root_.OAI.CoarseAssembly.vertexUnionDecidableEq _root_.OAI.NuclearUltrapower.strongDualInner
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped InnerProductSpace ComplexOrder
namespace NuclearUltrapower.SOS.ElementarySpectral

section Hilbert
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem deltaOp_energy_ca (ρ : E →* (H ≃ₗᵢ[ℂ] H)) (x : H) :
    (inner ℂ x (deltaOp ρ x)).re = SOSEnergy.energy eGenSet ρ x / 2 := by
  sorry

end Hilbert
end NuclearUltrapower.SOS.ElementarySpectral
end
end

end OAI
end
