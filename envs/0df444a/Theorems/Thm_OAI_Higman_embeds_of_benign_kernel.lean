-- Prove2me | Theorems.Thm_OAI_Higman_embeds_of_benign_kernel
-- name    : OAI.Higman.embeds_of_benign_kernel
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-18T19:46:34.868003+00:00
-- url     : https://prove2.me/theorems/e37f9808-0e37-46bf-94d3-eaa5fb2a4ea3
-- title:
--   Higman — a finitely generated group whose relation subgroup is benign embeds in a finitely presented group
-- statement:
--   A subgroup $A$ of a group $G$ is *benign* (`IsBenign A`, Higman's notion) if there are a finitely presented group $K$ (in the same universe as $G$), an injective homomorphism $i : G \to K$ and a finitely generated subgroup $B \le K$ with $i^{-1}(B) = A$.
--
--   **Statement.** Let $\iota$ be a finite type (in `Type u`), $D$ a group and $q : F(\iota) \to D$ a surjective homomorphism from the free group on $\iota$. If the kernel of $q$ is benign in $F(\iota)$, then $D$ has an injective homomorphism into some finitely presented group $K$ (in `Type u`).
--
--   This is the step of Higman's embedding theorem (Higman 1961) that turns benignity of the relations into an embedding.
--
--   Lean: `OAI.Higman.embeds_of_benign_kernel`, OpenAI's theorem of that name (in `lean/OAI/GroupTheory/UniversalGroup/RopeTrick.lean`). `IsBenign` comes from the definitions bundle `OAIQWUFI000` of this split; everything else is Mathlib.
-- source:
--   G. Higman, Subgroups of finitely presented groups, Proc. Roy. Soc. London Ser. A 262 (1961); Lean proof: OpenAI, A universal group of type F∞, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 250; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-universal-group-of-type-F-infinity-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/GroupTheory/UniversalGroup/RopeTrick.lean (declaration OAI.Higman.embeds_of_benign_kernel)

import Mathlib
import Definitions.Def_OAIQWUFI000

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u v w x

namespace Higman
variable {G : Type u} [Group G]

theorem embeds_of_benign_kernel {ι : Type u} [Finite ι]
    {D : Type v} [Group D] (q : FreeGroup ι →* D) (hq : Function.Surjective q)
    (hben : IsBenign q.ker) :
    ∃ (K : Type u) (_ : Group K) (_ : Group.IsFinitelyPresented K)
      (i : D →* K), Function.Injective i := by
  sorry

end Higman

end OAI
end
