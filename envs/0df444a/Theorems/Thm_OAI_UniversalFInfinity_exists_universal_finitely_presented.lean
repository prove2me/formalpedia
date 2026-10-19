-- Prove2me | Theorems.Thm_OAI_UniversalFInfinity_exists_universal_finitely_presented
-- name    : OAI.UniversalFInfinity.exists_universal_finitely_presented
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-18T19:45:18.496064+00:00
-- url     : https://prove2.me/theorems/8788c6cc-0855-4cab-bdc8-3404fb72f302
-- title:
--   Higman's universal finitely presented group — one finitely presented group contains a copy of every finitely presented group
-- statement:
--   **Statement.** There is a finitely presented group $U$ (in `Type`) such that every finitely presented group $G$, in any universe `Type z`, has an injective homomorphism $G \to U$.
--
--   Here "finitely presented" is Mathlib's `Group.IsFinitelyPresented`. This is Higman's universal finitely presented group (Higman 1961), a consequence of his embedding theorem.
--
--   Lean: `OAI.UniversalFInfinity.exists_universal_finitely_presented`, OpenAI's theorem of that name (in `lean/OAI/GroupTheory/UniversalGroup/UniversalPresentation.lean`). The statement uses only Mathlib.
-- source:
--   G. Higman, Subgroups of finitely presented groups, Proc. Roy. Soc. London Ser. A 262 (1961); Lean proof: OpenAI, A universal group of type F∞, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 250; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-universal-group-of-type-F-infinity-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/GroupTheory/UniversalGroup/UniversalPresentation.lean (declaration OAI.UniversalFInfinity.exists_universal_finitely_presented)

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

namespace UniversalFInfinity
universe z

theorem exists_universal_finitely_presented :
    ∃ (U : Type) (_ : Group U) (_ : Group.IsFinitelyPresented U),
      ∀ (G : Type z) [Group G] [Group.IsFinitelyPresented G],
        ∃ i : G →* U, Function.Injective i := by
  sorry

end UniversalFInfinity

end
end UniversalFinitelyPresentedProof

end OAI
end
