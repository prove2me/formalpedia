-- Prove2me | Theorems.Thm_OAI_LinearListHadwiger_SmallList_additive_deletion_or_obstruction
-- name    : OAI.LinearListHadwiger.SmallList.additive_deletion_or_obstruction
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-19T02:49:35.447823+00:00
-- url     : https://prove2.me/theorems/d3a78097-cd33-4af0-96a8-60a6882574cf
-- title:
--   Deleting a small set and a degenerate set costs O(t) list colours, or there is a fractional obstruction (OpenAI, linear list Hadwiger)
-- statement:
--   There is a $t_0$ such that the following holds for all $t \ge t_0$, every finite graph $G$ with $h(G) < t$, disjoint vertex sets $X$ and $Y$, and every $d$. Assume:
--   - $|X| \le t^{11/10}$;
--   - $G$ is $(dt)$-degenerate on $Y$, meaning every nonempty subset of $Y$ has a vertex with at most $dt$ neighbours in it (`DegenerateOn G Y (d*t)`);
--   - every vertex outside $X \cup Y$ has at most $dt$ neighbours in $Y$.
--
--   Then one of two things holds. The first possibility is
--   $$\chi_{\mathrm{list}}(G) \le \chi_{\mathrm{list}}\bigl(G - (X\cup Y)\bigr) + (4\cdot 32768 + d + 5)\,t.$$
--   The second is that $G$ has a fractional obstruction (`FractionalObstruction G`): an induced subgraph whose fractional chromatic number exceeds four times its Hadwiger number.
--
--   `listChromaticNumber` and `hadwigerNumber` come from the published bundle `Def_ListHadwiger`. `DegenerateOn` and `FractionalObstruction` come from the definitions bundle `OAIQWLLH000` of this split. The carver publishes this lemma as an intermediate statement so that each proof fits the platform's verifier.
--
--   Lean: `OAI.LinearListHadwiger.SmallList.additive_deletion_or_obstruction`, OpenAI's theorem of that name in `lean/OAI/Combinatorics/ListHadwiger/HistoryBounds.lean`.
-- source:
--   OpenAI, A linear list-coloring bound in terms of the Hadwiger number, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 157; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-linear-list-coloring-bound-in-terms-of-the-Hadwiger-number-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/ListHadwiger/HistoryBounds.lean (declaration OAI.LinearListHadwiger.SmallList.additive_deletion_or_obstruction)

import Mathlib
import Definitions.Def_ListHadwiger
import Definitions.Def_OAIQWLLH000

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace LinearListHadwiger.SmallList
open Finset

attribute [local instance] Classical.propDecidable

theorem additive_deletion_or_obstruction : ∃ t₀ : ℕ, ∀ t : ℕ, t₀ ≤ t →
    ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) (X Y : Finset V) (d : ℕ),
    hadwigerNumber G < t → (X.card:ℝ) ≤ (t:ℝ)^(11/10:ℝ) → Disjoint X Y →
    DegenerateOn G Y (d*t) →
    (∀ v ∉ X∪Y, (Y.filter (G.Adj v)).card ≤ d*t) →
    listChromaticNumber G ≤ listChromaticNumber (G.induce (↑(univ\(X∪Y)):Set V)) +
      (4*32768+d+5)*t ∨ FractionalObstruction G := by
  sorry

end LinearListHadwiger.SmallList

end OAI
end
