-- Prove2me | Theorems.Thm_OAI_Higman_benign_iff_centralExtension_embeds
-- name    : OAI.Higman.benign_iff_centralExtension_embeds
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-18T19:46:09.323592+00:00
-- url     : https://prove2.me/theorems/a5101be5-e55e-4d08-af6d-aa0a0b08746d
-- title:
--   A subgroup is benign if and only if the HNN extension centralizing it embeds in a finitely presented group
-- statement:
--   A subgroup $A$ of a group $G$ is *benign* (`IsBenign A`, Higman's notion) if there are a finitely presented group $K$ (in the same universe as $G$), an injective homomorphism $i : G \to K$ and a finitely generated subgroup $B \le K$ with $i^{-1}(B) = A$. `CentralExtension G A` is Mathlib's HNN extension `HNNExtension G A A (MulEquiv.refl A)`: $G$ with one new generator $t$ subject to $t a t^{-1} = a$ for $a \in A$.
--
--   **Statement.** For a group $G$ (in `Type u`) and a subgroup $A \le G$: $A$ is benign if and only if `CentralExtension G A` has an injective homomorphism into some finitely presented group $K$ (in `Type u`).
--
--   Lean: `OAI.Higman.benign_iff_centralExtension_embeds`, OpenAI's theorem of that name (in `lean/OAI/GroupTheory/UniversalGroup/Benign.lean`). `IsBenign` and `CentralExtension` come from the definitions bundle `OAIQWUFI000` of this split; everything else is Mathlib.
-- source:
--   G. Higman, Subgroups of finitely presented groups, Proc. Roy. Soc. London Ser. A 262 (1961); Lean proof: OpenAI, A universal group of type F∞, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 250; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-universal-group-of-type-F-infinity-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/GroupTheory/UniversalGroup/Benign.lean (declaration OAI.Higman.benign_iff_centralExtension_embeds)

import Mathlib
import Definitions.Def_OAIQWUFI000

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section UniversalFinitelyPresentedProof
universe u v w x

namespace Higman
variable {G : Type u} [Group G] {A : Subgroup G}

theorem benign_iff_centralExtension_embeds : IsBenign A ↔
    ∃ (K : Type u) (_ : Group K) (_ : Group.IsFinitelyPresented K)
      (j : CentralExtension G A →* K), Function.Injective j := by
  sorry

end Higman

end UniversalFinitelyPresentedProof

end OAI
end
