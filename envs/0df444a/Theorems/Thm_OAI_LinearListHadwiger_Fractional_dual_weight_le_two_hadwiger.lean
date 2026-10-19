-- Prove2me | Theorems.Thm_OAI_LinearListHadwiger_Fractional_dual_weight_le_two_hadwiger
-- name    : OAI.LinearListHadwiger.Fractional.dual_weight_le_two_hadwiger
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-19T02:45:05.730614+00:00
-- url     : https://prove2.me/theorems/942190a2-771d-416a-bd2e-5f851d07d52e
-- title:
--   Reed–Seymour, dual form: a vertex weighting with weight at most 1 on every stable set has total weight at most 2·had(G)
-- statement:
--   Let $G$ be a simple graph on a finite vertex type $V$ with decidable equality, and let $w : V \to \mathbb{R}$ be a weighting of the vertices. Suppose every stable set $I$ has weight at most $1$: for every finite set $I$ containing no edge of $G$, $\sum_{v \in I} w(v) \le 1$. Then
--   $$\sum_{v \in V} w(v) \;\le\; 2\, h(G),$$
--   where $h(G)$ = `hadwigerNumber G` is the Hadwiger number. That is the largest $t$ such that $G$ has $t$ pairwise disjoint, pairwise touching connected vertex sets, i.e. a $K_t$ minor.
--
--   The weights need not be nonnegative. By linear-programming duality, this is equivalent to the bound $\chi_f(G) \le 2h(G)$ on the fractional chromatic number (Reed–Seymour 1998). That bound is the companion statement `OAI.LinearListHadwiger.Fractional.fractional_chromatic_le_two_hadwiger`.
--
--   `hadwigerNumber` comes from the published bundle `Def_ListHadwiger`. Otherwise the statement uses only Mathlib.
--
--   Lean: `OAI.LinearListHadwiger.Fractional.dual_weight_le_two_hadwiger`. It is the dual half of OpenAI's proof of `number_le_two_hadwiger` in `lean/OAI/Combinatorics/ListHadwiger/Main.lean`, stated for every weighting, with OpenAI's definition `Stable` written out.
-- source:
--   B. Reed and P. Seymour, Fractional colouring and Hadwiger's conjecture, J. Combin. Theory Ser. B 74 (1998), 147–152. Lean proof: OpenAI, A linear list-coloring bound in terms of the Hadwiger number, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 157; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-linear-list-coloring-bound-in-terms-of-the-Hadwiger-number-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/ListHadwiger/Main.lean (declaration OAI.LinearListHadwiger.Fractional.number_le_two_hadwiger and its dual form ReedSeymour.dual_weight_bound)

import Mathlib
import Definitions.Def_ListHadwiger

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace LinearListHadwiger

namespace Fractional
variable {V : Type} [Fintype V] [DecidableEq V]

theorem dual_weight_le_two_hadwiger (G : SimpleGraph V) (w : V → ℝ)
    (hw : ∀ I : Finset V, (∀ v ∈ I, ∀ u ∈ I, ¬G.Adj v u) → ∑ v ∈ I, w v ≤ 1) :
    ∑ v, w v ≤ 2 * (hadwigerNumber G : ℝ) := by
  sorry

end Fractional

end LinearListHadwiger

end OAI
end
