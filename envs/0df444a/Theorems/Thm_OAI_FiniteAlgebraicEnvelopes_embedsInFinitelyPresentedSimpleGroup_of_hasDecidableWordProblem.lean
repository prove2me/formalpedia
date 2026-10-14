-- Prove2me | Theorems.Thm_OAI_FiniteAlgebraicEnvelopes_embedsInFinitelyPresentedSimpleGroup_of_hasDecidableWordProblem
-- name    : OAI.FiniteAlgebraicEnvelopes.embedsInFinitelyPresentedSimpleGroup_of_hasDecidableWordProblem
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-10-12T15:41:24.591306+00:00
-- url     : https://prove2.me/theorems/d9d8eb37-cf54-44e8-8b50-4cb12ce7e142
-- title:
--   Boone–Higman, forward direction
-- statement:
--   This is the forward direction of Theorem 1.1 of the cited preprint, which states the Boone–Higman conjecture as an equivalence.
--
--   Let $G$ be a finitely generated group with decidable word problem: there is a finite tuple of generators for which the set of words evaluating to the identity is a computable predicate. The statement asserts that $G$ then embeds into some finitely presented simple group $H$ (in the same universe), via an injective group homomorphism.
--
--   $$
--   G \text{ has decidable word problem} \implies \exists\, H,\ H \text{ finitely presented and simple},\ \exists\, \varphi : G \hookrightarrow H.
--   $$
--
--   This direction carries the substantive content of the conjecture (the converse is classical): Boone and Higman's own construction gives a finitely generated simple overgroup, but no finite presentation; the preprint's route produces a finitely presented group with a faithful two-transitive action built from a direct limit of finitely presented algebras (its own Theorem 1.2), combined with Zaremsky's finite-presentation criterion for twisted Brin–Thompson groups.
--
--   **Formalization Note** `HasDecidableWordProblem` and `EmbedsInFinitelyPresentedSimpleGroup` are the definitions already published for this mission's goal (`Definitions.Def_BooneHigman`); this theorem is exactly the `→` half of that goal's iff, isolated so it can be attacked independently of the (classical) converse.
-- source:
--   OpenAI, *Finite algebraic envelopes and the Boone–Higman conjecture*, OpenAI Math Release preprint, September 23, 2026, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Finite-algebraic-envelopes-and-the-Boone-Higman-conjecture-September-23-2026/paper.pdf (Theorem 1.1); the conjecture is due to W. W. Boone and G. Higman, An algebraic characterization of groups with soluble word problem, J. Austral. Math. Soc. 18 (1974), https://doi.org/10.1017/S1446788700019108.

import Mathlib
import Definitions.Def_BooneHigman

namespace OAI

namespace FiniteAlgebraicEnvelopes

universe u

theorem embedsInFinitelyPresentedSimpleGroup_of_hasDecidableWordProblem
    (GroupType : Type u) [Group GroupType] [Group.FG GroupType]
    (h : HasDecidableWordProblem GroupType) :
    EmbedsInFinitelyPresentedSimpleGroup GroupType := by
  sorry

end FiniteAlgebraicEnvelopes
end OAI
