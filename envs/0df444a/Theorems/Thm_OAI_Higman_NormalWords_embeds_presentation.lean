-- Prove2me | Theorems.Thm_OAI_Higman_NormalWords_embeds_presentation
-- name    : OAI.Higman.NormalWords.embeds_presentation
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-18T19:45:52.32436+00:00
-- url     : https://prove2.me/theorems/85476ce2-8b7f-42d7-a710-d6b40be6fe58
-- title:
--   Higman's embedding theorem — a group with three generators and a computably enumerated set of relators embeds in a finitely presented group
-- statement:
--   Let `Alphabet` $= $ `Bool ⊕ Unit` (three letters) and let `Raw` $= $ `List (Alphabet × Bool)` be the type of words in these letters and their inverses. Each word $w$ gives the element `FreeGroup.mk w` of the free group on three generators.
--
--   **Statement.** Let $r : \mathbb N \to$ `Raw` be computable (Mathlib's `Computable`). Then the group
--   $$P_r \;=\; \bigl\langle\, \text{Alphabet} \ \big|\ r(0),\, r(1),\, r(2),\, \dots \bigr\rangle$$
--   (Mathlib's `PresentedGroup` on the set of relators $\{$`FreeGroup.mk (r n)` $: n \in \mathbb N\}$) has an injective homomorphism into some finitely presented group $K$ (with $K$ in `Type`).
--
--   This is Higman's embedding theorem (Higman 1961), that a recursively presented group embeds in a finitely presented group, stated here for groups with three generators.
--
--   Lean: `OAI.Higman.NormalWords.embeds_presentation`, OpenAI's theorem of that name (in `lean/OAI/GroupTheory/UniversalGroup/HigmanEmbedding.lean`). `Alphabet` and `Raw` come from the definitions bundle `OAIQWUFI000` of this split; everything else is Mathlib.
-- source:
--   G. Higman, Subgroups of finitely presented groups, Proc. Roy. Soc. London Ser. A 262 (1961); Lean proof: OpenAI, A universal group of type F∞, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 250; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-universal-group-of-type-F-infinity-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/GroupTheory/UniversalGroup/HigmanEmbedding.lean (declaration OAI.Higman.NormalWords.embeds_presentation)

import Mathlib
import Definitions.Def_OAIQWUFI000

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u v w x

noncomputable section

namespace Higman.NormalWords

theorem embeds_presentation (r : ℕ → Raw) (hr : Computable r) :
    ∃ (K : Type) (_ : Group K) (_ : Group.IsFinitelyPresented K)
      (i : PresentedGroup (Set.range (fun n ↦ FreeGroup.mk (r n))) →* K),
      Function.Injective i := by
  sorry

end Higman.NormalWords

end

end OAI
end
