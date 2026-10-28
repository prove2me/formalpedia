-- Prove2me | Theorems.Thm_OAI_FiniteAlgebraicEnvelopes_envelope
-- name    : OAI.FiniteAlgebraicEnvelopes.envelope
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-24T19:24:05.276982+00:00
-- url     : https://prove2.me/theorems/eb1ff0d0-8124-439d-a32e-3188a13300fa
-- title:
--   Theorem 1.2: every finitely generated group with decidable word problem has a finitely presented two-transitive envelope (OpenAI Boone–Higman)
-- statement:
--   The paper's Theorem 1.2 ("Every finitely generated group with decidable word problem embeds in a finitely presented group admitting a faithful two-transitive action on a countably infinite set with finitely generated point stabilizers"), as OpenAI formalized it. It is an intermediate statement of the split of OpenAI's proof of `OAI.FiniteAlgebraicEnvelopes.main` (the paper's Theorem 1.1, the Boone–Higman equivalence).
--
--   **Notation.** `HasDecidableWordProblem G` (published bundle `Def_BooneHigman`) says that $G$ has a finite generating family $t : \mathrm{Fin}\ n \to G$ for which equality to $1$ of words in the $t_i^{\pm 1}$ is a computable predicate. `HasActionEnvelope G` (definitions bundle `OAIFAE001` of this split) says that there are a group $\Gamma$ and a $\Gamma$-set $X$, both in the universe of $G$, such that $\Gamma$ is finitely presented, $X$ is countable and infinite, the action is faithful, any pair of distinct points can be moved to any pair of distinct points by one element of $\Gamma$, every point stabilizer is finitely generated, and there is an injective homomorphism $G \to \Gamma$.
--
--   **The statement.** For every finitely generated group $G$ with decidable word problem, `HasActionEnvelope G` holds.
--
--   The mission's own form of this theorem, `OAI.FiniteAlgebraicEnvelopes.theorem_1_2` (no separate finite-generation hypothesis, two-transitivity as `MulAction.IsMultiplyPretransitive Γ X 2`), follows from this statement in a few lines.
-- source:
--   OpenAI, Finite algebraic envelopes and the Boone–Higman conjecture, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 250; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Finite-algebraic-envelopes-and-the-Boone-Higman-conjecture-September-23-2026/paper.pdf, Theorem 1.2; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/GroupTheory/BooneHigman/ActionEnvelope.lean (declaration OAI.FiniteAlgebraicEnvelopes.envelope)

import Mathlib
import Definitions.Def_BooneHigman
import Definitions.Def_OAIFAE001

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace FiniteAlgebraicEnvelopes

section
universe u

theorem envelope (G : Type u) [Group G] [Group.FG G]
    (hG : HasDecidableWordProblem G) : HasActionEnvelope G := by
  sorry

open scoped commutatorElement

end

end FiniteAlgebraicEnvelopes

end

end OAI
end
