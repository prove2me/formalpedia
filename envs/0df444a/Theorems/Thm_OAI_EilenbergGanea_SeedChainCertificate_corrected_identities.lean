-- Prove2me | Theorems.Thm_OAI_EilenbergGanea_SeedChainCertificate_corrected_identities
-- name    : OAI.EilenbergGanea.SeedChainCertificate.corrected_identities
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-25T03:06:36.011769+00:00
-- url     : https://prove2.me/theorems/1ec2ad47-4f6a-4b7a-b87b-9af0eeb0e0bb
-- title:
--   Seed chain certificate: the corrected contraction identities on triangles and edges (OpenAI Eilenberg–Ganea)
-- statement:
--   The upper identities of OpenAI's explicit augmented chain contraction of the flag complex $L$ of the paper's Section 4, which shows $L$ integrally acyclic. It is an intermediate statement of the split of OpenAI's proof of `OAI.EilenbergGanea.source_main`, published on its own because the chain contraction (a definition) rests on it.
--
--   **Notation** (definitions bundles of this split, namespace `OAI.EilenbergGanea.SeedChainCertificate`). The flag complex (the order complex of the 103 cells of the seed triangulation `seedGraph`) has 103 vertices, 372 edges and 270 triangles. `d₁` and `d₂` are its boundary maps $\mathbb Z^{372} \to \mathbb Z^{103}$ and $\mathbb Z^{270} \to \mathbb Z^{372}$ (`rowsMap d1Row`, `rowsMap d2Row`); `h₀` and `h₁` are the contraction matrices decoded from the packed tables `h0CodeData` and `h1CodeData`; and `h₁' = h₁ ∘ (id − h₀ ∘ d₁)`.
--
--   **The statement.** For every triangle $t$, $h_1'(d_2(\delta_t)) = \delta_t$; and for every edge $e$, $d_2(h_1'(\delta_e)) + h_0(d_1(\delta_e)) = \delta_e$, where $\delta$ denotes an indicator (`Pi.single _ 1`).
-- source:
--   OpenAI, A finitely generated counterexample to the Eilenberg–Ganea conjecture, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 249; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-finitely-generated-counterexample-to-the-Eilenberg-Ganea-conjecture-September-23-2026/paper.pdf, Section 4; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Topology/EilenbergGanea/SeedContraction.lean (declaration OAI.EilenbergGanea.SeedChainCertificate.corrected_identities)

import Mathlib
import Definitions.Def_OAIEGC000

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

attribute [local instance] OAI.EilenbergGanea.SeedChainCertificate.instDecidableEqFinOfNatNat_solutions_1
attribute [local instance] OAI.EilenbergGanea.SeedChainCertificate.instDecidableEqFinOfNatNat_solutions_2
theorem corrected_identities :
    (∀ t, h₁' (d₂ (Pi.single t 1)) = Pi.single t 1) ∧
    (∀ e, d₂ (h₁' (Pi.single e 1)) + h₀ (d₁ (Pi.single e 1)) = Pi.single e 1) := by
  sorry

end EilenbergGanea.SeedChainCertificate

end

end OAI
end
