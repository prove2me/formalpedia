-- Prove2me | Theorems.Thm_OAI_Higman_NormalWords_benign_normalClosure
-- name    : OAI.Higman.NormalWords.benign_normalClosure
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-18T19:45:44.780747+00:00
-- url     : https://prove2.me/theorems/45880534-7427-45e7-8024-3557e321f13a
-- title:
--   The normal closure of a computably enumerated set of words on three letters is benign in the free group
-- statement:
--   Let `Alphabet` $= $ `Bool ⊕ Unit` (three letters) and `Raw` $= $ `List (Alphabet × Bool)`, the words in these letters and their inverses. A subgroup $A$ of a group $G$ is *benign* (`IsBenign A`, Higman's notion) if there are a finitely presented group $K$ (in the same universe as $G$), an injective homomorphism $i : G \to K$ and a finitely generated subgroup $B \le K$ with $i^{-1}(B) = A$.
--
--   **Statement.** Let $r : \mathbb N \to$ `Raw` be computable (Mathlib's `Computable`). Then the normal closure of $\{$`FreeGroup.mk (r n)` $: n \in \mathbb N\}$ in the free group on `Alphabet` is benign.
--
--   This is the core step of Higman's embedding theorem (Higman 1961), that recursively enumerable relations generate a benign normal subgroup, stated here for words on three letters.
--
--   Lean: `OAI.Higman.NormalWords.benign_normalClosure`, OpenAI's theorem of that name (in `lean/OAI/GroupTheory/UniversalGroup/HigmanEmbedding.lean`). `Alphabet`, `Raw` and `IsBenign` come from the definitions bundle `OAIQWUFI000` of this split; everything else is Mathlib.
-- source:
--   G. Higman, Subgroups of finitely presented groups, Proc. Roy. Soc. London Ser. A 262 (1961); Lean proof: OpenAI, A universal group of type F∞, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 250; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-universal-group-of-type-F-infinity-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/GroupTheory/UniversalGroup/HigmanEmbedding.lean (declaration OAI.Higman.NormalWords.benign_normalClosure)

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

theorem benign_normalClosure (r : ℕ → Raw) (hr : Computable r) :
    IsBenign (Subgroup.normalClosure (Set.range (fun n ↦ FreeGroup.mk (r n)))) := by
  sorry

end Higman.NormalWords

end

end OAI
end
