-- Prove2me | Theorems.Thm_OAI_UniversalFInfinity_CountableOvergroup_countable_embeds_three_generated
-- name    : OAI.UniversalFInfinity.CountableOvergroup.countable_embeds_three_generated
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-18T19:45:13.80267+00:00
-- url     : https://prove2.me/theorems/9e997ba4-3778-4806-a213-5cecda41f2ff
-- title:
--   Higman–Neumann–Neumann — every countable group embeds in a finitely generated group
-- statement:
--   **Statement.** Let $C$ be a countable group (in `Type u`). Then there are a finitely generated group $V$ (Mathlib's `Group.FG`, also in `Type u`) and an injective homomorphism $C \to V$.
--
--   This is the embedding theorem of Higman, B. H. Neumann and H. Neumann (1949), in the form "finitely generated". The declaration's name refers to three generators, but the Lean statement asserts only that $V$ is finitely generated.
--
--   Lean: `OAI.UniversalFInfinity.CountableOvergroup.countable_embeds_three_generated`, OpenAI's theorem of that name (in `lean/OAI/GroupTheory/UniversalGroup/UniversalPresentation.lean`). The statement uses only Mathlib.
-- source:
--   G. Higman, B. H. Neumann, H. Neumann, Embedding theorems for groups, J. London Math. Soc. 24 (1949); Lean proof: OpenAI, A universal group of type F∞, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 250; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-universal-group-of-type-F-infinity-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/GroupTheory/UniversalGroup/UniversalPresentation.lean (declaration OAI.UniversalFInfinity.CountableOvergroup.countable_embeds_three_generated)

import Mathlib

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section UniversalFinitelyPresentedProof
universe u v w x
noncomputable section

namespace UniversalFInfinity.CountableOvergroup
open Monoid
variable {C : Type u} [Group C] (c : ℕ → C)

theorem countable_embeds_three_generated [Countable C] :
    ∃ (V : Type u) (_ : Group V) (_ : Group.FG V),
      ∃ e : C →* V, Function.Injective e := by
  sorry

end UniversalFInfinity.CountableOvergroup

end
end UniversalFinitelyPresentedProof

end OAI
end
