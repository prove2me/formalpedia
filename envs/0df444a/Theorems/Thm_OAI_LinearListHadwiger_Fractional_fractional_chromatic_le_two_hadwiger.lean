-- Prove2me | Theorems.Thm_OAI_LinearListHadwiger_Fractional_fractional_chromatic_le_two_hadwiger
-- name    : OAI.LinearListHadwiger.Fractional.fractional_chromatic_le_two_hadwiger
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-19T02:45:07.710716+00:00
-- url     : https://prove2.me/theorems/2e3980db-a774-4657-9ae7-0e2cc713f889
-- title:
--   Reed–Seymour: the fractional chromatic number is at most twice the Hadwiger number
-- statement:
--   Let $G$ be a simple graph on a finite vertex type $V$ with decidable equality. A fractional colouring is a weighting $\mu$ of the finite vertex sets with three properties:
--   - $\mu(I) \ge 0$ for every $I$;
--   - $\mu(I) = 0$ unless $I$ is stable, meaning it contains no edge of $G$;
--   - every vertex $v$ is covered with total weight at least $1$, that is $\sum_{I \ni v} \mu(I) \ge 1$.
--
--   The fractional chromatic number $\chi_f(G)$ is the infimum of the costs $\sum_I \mu(I)$ of fractional colourings. In Lean this is the `sInf` of the set of these costs. Then
--   $$\chi_f(G) \;\le\; 2\,h(G),$$
--   where $h(G)$ = `hadwigerNumber G` is the Hadwiger number, the order of the largest clique minor of $G$ (Reed–Seymour 1998).
--
--   `hadwigerNumber` comes from the published bundle `Def_ListHadwiger`. Otherwise the statement uses only Mathlib.
--
--   Lean: `OAI.LinearListHadwiger.Fractional.fractional_chromatic_le_two_hadwiger`. This is OpenAI's theorem `number_le_two_hadwiger` in `lean/OAI/Combinatorics/ListHadwiger/Main.lean`, with OpenAI's definitions `number`, `Cover`, `cost` and `Stable` written out.
-- source:
--   B. Reed and P. Seymour, Fractional colouring and Hadwiger's conjecture, J. Combin. Theory Ser. B 74 (1998), 147–152. Lean proof: OpenAI, A linear list-coloring bound in terms of the Hadwiger number, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 157; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-linear-list-coloring-bound-in-terms-of-the-Hadwiger-number-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/ListHadwiger/Main.lean (declaration OAI.LinearListHadwiger.Fractional.number_le_two_hadwiger, stated here with its definitions written out)

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

theorem fractional_chromatic_le_two_hadwiger (G : SimpleGraph V) :
    sInf {c : ℝ | ∃ μ : Finset V → ℝ,
      ((∀ I, 0 ≤ μ I) ∧ (∀ I, ¬(∀ v ∈ I, ∀ u ∈ I, ¬G.Adj v u) → μ I = 0) ∧
        ∀ v, 1 ≤ ∑ I, if v ∈ I then μ I else 0) ∧ ∑ I, μ I = c} ≤
      2 * (hadwigerNumber G : ℝ) := by
  sorry

end Fractional

end LinearListHadwiger

end OAI
end
