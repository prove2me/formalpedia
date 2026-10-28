-- Prove2me | Theorems.Thm_OAI_EilenbergGanea_SeedChainCertificate_bottom_identity
-- name    : OAI.EilenbergGanea.SeedChainCertificate.bottom_identity
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-25T03:04:30.53414+00:00
-- url     : https://prove2.me/theorems/fb0755b5-c5ab-457b-a155-8261ddaf8665
-- title:
--   Seed chain certificate: the bottom contraction identity d₁ ∘ h₀ = id − (vertex 0) on vertices (OpenAI Eilenberg–Ganea)
-- statement:
--   One identity of OpenAI's explicit augmented chain contraction of the flag complex $L$ of the paper's Section 4, which shows $L$ integrally acyclic. It is an intermediate statement of the split of OpenAI's proof of `OAI.EilenbergGanea.source_main`, published on its own because the chain contraction (a definition) rests on it.
--
--   **Notation** (definitions bundles of this split, namespace `OAI.EilenbergGanea.SeedChainCertificate`). The flag complex (the order complex of the 103 cells of the seed triangulation `seedGraph`) has 103 vertices, 372 edges and 270 triangles. `d₁ : (Fin 372 → ℤ) →ₗ[ℤ] (Fin 103 → ℤ)` is its first boundary map (`rowsMap d1Row`), and `h₀ : (Fin 103 → ℤ) →ₗ[ℤ] (Fin 372 → ℤ)` is the contraction matrix decoded from the packed table `h0CodeData`.
--
--   **The statement.** For every vertex $v$, $d_1(h_0(\delta_v)) = \delta_v - \delta_0$, where $\delta_v$ is the indicator of $v$ (`Pi.single v 1`).
-- source:
--   OpenAI, A finitely generated counterexample to the Eilenberg–Ganea conjecture, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 249; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-finitely-generated-counterexample-to-the-Eilenberg-Ganea-conjecture-September-23-2026/paper.pdf, Section 4; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Topology/EilenbergGanea/SeedContraction.lean (declaration OAI.EilenbergGanea.SeedChainCertificate.bottom_identity)

import Mathlib
import Definitions.Def_OAIEG011

section

attribute [-instance] _root_.OAI.EilenbergGanea.CWCollar.positiveRealsContractible
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Classical Set

namespace EilenbergGanea.SeedChainCertificate

attribute [local instance] OAI.EilenbergGanea.SeedChainCertificate.instDecidableEqFinOfNatNat_solutions
theorem bottom_identity (v : Fin 103) : d₁ (h₀ (Pi.single v 1)) = Pi.single v 1 - Pi.single 0 1 := by
  sorry

end EilenbergGanea.SeedChainCertificate

end

end OAI
end
