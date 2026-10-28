-- Prove2me | Theorems.Thm_OAI_EilenbergGanea_aligned_presentation_small_transport
-- name    : OAI.EilenbergGanea.aligned_presentation_small_transport
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-25T00:17:02.566818+00:00
-- url     : https://prove2.me/theorems/912c8be5-3c45-49f0-b53d-b31ff65fcbba
-- title:
--   OAI.EilenbergGanea.aligned_presentation_small_transport: intermediate lemma from OpenAI, A finitely generated counterexample to the Eilenberg–Ganea conjecture
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.EilenbergGanea.source_main`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A finitely generated counterexample to the Eilenberg–Ganea conjecture*, OpenAI Math Release, September 23, 2026, result family 249, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.EilenbergGanea.aligned_presentation_small_transport` of [lean/OAI/Topology/EilenbergGanea/PresentationComparison.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Topology/EilenbergGanea/PresentationComparison.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.EilenbergGanea`, with `open Classical Set Filter Topology MeasureTheory`, `open scoped Quaternion ContDiff`, `open scoped Quaternion`):
--
--   ```lean
--   theorem aligned_presentation_small_transport
--       (v : S ⊕ T → Γ) (r : Z ⊕ R → FreeGroup (S ⊕ T)) (z : Z → FreeGroup S)
--       (hvT : ∀ t, v (.inr t) = 1)
--       (hr : ∀ i, wordValue v (r i) = 1)
--       (hz : ∀ i, wordValue (fun s => v (.inl s)) (z i) = 1)
--       (hp : (wordValue v).ker = Subgroup.normalClosure (Set.range r))
--       (hinj : Function.Injective (relatorChainMap v r))
--       (hchain : ∀ i, pathChain v (FreeGroup.map Sum.inl (z i)) 1 = pathChain v (r (.inl i)) 1)
--       (Q : BasedChains Γ R ≃ₗ[ℤ] BasedChains Γ T)
--       (hQ : Q.toLinearMap = extraRelatorMap v (fun i => r (.inr i))) :
--       ∃ η : ℝ, 0 < η ∧ ∀ a : Γ → S → SU2,
--         (∀ g s, ‖(a g s : ℍ)-1‖ < η) →
--         (∀ i g, pathProduct (fun s => v (.inl s)) a (z i) g = 1) →
--         ∀ w : FreeGroup S, wordValue (fun s => v (.inl s)) w = 1 → ∀ g,
--           pathProduct (fun s => v (.inl s)) a w g = 1
--   ```
--
--   **Definitions.** The statement is written with `OAI.EilenbergGanea.BasedChains` and `OAI.EilenbergGanea.SU2` (definitions bundle `OAIEG000` of this split); `OAI.EilenbergGanea.pathChain`, `OAI.EilenbergGanea.pathProduct`, `OAI.EilenbergGanea.relatorChainMap` and `OAI.EilenbergGanea.wordValue` (definitions bundle `OAIEG001` of this split); `OAI.EilenbergGanea.extraRelatorMap` (definitions bundle `OAIEG011` of this split).
--
--   **Used by.** The proof of `OAI.EilenbergGanea.boundary_basis_small_transport` of this split imports it.
-- source:
--   OpenAI, A finitely generated counterexample to the Eilenberg–Ganea conjecture, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 249; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-finitely-generated-counterexample-to-the-Eilenberg-Ganea-conjecture-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Topology/EilenbergGanea/PresentationComparison.lean (declaration OAI.EilenbergGanea.aligned_presentation_small_transport)

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

universe u

open Classical Set Filter Topology MeasureTheory
open scoped Quaternion ContDiff

namespace EilenbergGanea
open scoped Quaternion
section AlignedComparison
variable {Γ : Type u} {S T Z R : Type*} [Group Γ] [Group.ResiduallyFinite Γ] [Fintype Z]

theorem aligned_presentation_small_transport
    (v : S ⊕ T → Γ) (r : Z ⊕ R → FreeGroup (S ⊕ T)) (z : Z → FreeGroup S)
    (hvT : ∀ t, v (.inr t) = 1)
    (hr : ∀ i, wordValue v (r i) = 1)
    (hz : ∀ i, wordValue (fun s => v (.inl s)) (z i) = 1)
    (hp : (wordValue v).ker = Subgroup.normalClosure (Set.range r))
    (hinj : Function.Injective (relatorChainMap v r))
    (hchain : ∀ i, pathChain v (FreeGroup.map Sum.inl (z i)) 1 = pathChain v (r (.inl i)) 1)
    (Q : BasedChains Γ R ≃ₗ[ℤ] BasedChains Γ T)
    (hQ : Q.toLinearMap = extraRelatorMap v (fun i => r (.inr i))) :
    ∃ η : ℝ, 0 < η ∧ ∀ a : Γ → S → SU2,
      (∀ g s, ‖(a g s : ℍ)-1‖ < η) →
      (∀ i g, pathProduct (fun s => v (.inl s)) a (z i) g = 1) →
      ∀ w : FreeGroup S, wordValue (fun s => v (.inl s)) w = 1 → ∀ g,
        pathProduct (fun s => v (.inl s)) a w g = 1 := by
  sorry

end AlignedComparison
end EilenbergGanea

end

end OAI
end
