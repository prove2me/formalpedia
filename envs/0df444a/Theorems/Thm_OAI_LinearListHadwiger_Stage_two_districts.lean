-- Prove2me | Theorems.Thm_OAI_LinearListHadwiger_Stage_two_districts
-- name    : OAI.LinearListHadwiger.Stage.two_districts
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-19T02:47:39.066688+00:00
-- url     : https://prove2.me/theorems/c04b1964-8d24-423d-b4aa-a226084f251c
-- title:
--   Two disjoint small highly connected districts, or a fractional obstruction (OpenAI, linear list Hadwiger)
-- statement:
--   For every $K > 0$ there is a $D > \max(400\cdot 3202,\ 12800K)$ and a $T$ such that the following holds for all $t \ge T$. Let $G$ be a finite graph with $h(G) < t$, and let $S$ be a vertex set with $\ell(S) > (2D + 4\cdot 32768 + 5)t + 2$, where $\ell(S)$ is the list chromatic number of $G[S]$. Then one of two things holds:
--   - there are disjoint sets $J, H \subseteq S$, each $Kt$-connected and each of size at most $t^{53/50}$;
--   - $G$ has a fractional obstruction.
--
--   `ell`, `KConnectedOn` and `FractionalObstruction` come from the definitions bundle `OAIQWLLH000` of this split, and `hadwigerNumber` comes from the published bundle `Def_ListHadwiger`. The carver publishes this lemma as an intermediate statement so that each proof fits the platform's verifier.
--
--   Lean: `OAI.LinearListHadwiger.Stage.two_districts`, OpenAI's theorem of that name in `lean/OAI/Combinatorics/ListHadwiger/Stage.lean`.
-- source:
--   OpenAI, A linear list-coloring bound in terms of the Hadwiger number, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 157; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-linear-list-coloring-bound-in-terms-of-the-Hadwiger-number-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/ListHadwiger/Stage.lean (declaration OAI.LinearListHadwiger.Stage.two_districts)

import Mathlib
import Definitions.Def_ListHadwiger
import Definitions.Def_OAIQWLLH000

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace LinearListHadwiger.Stage
open Finset SmallList
attribute [local instance] Classical.propDecidable

theorem two_districts : ∀ K : ℕ, 0<K → ∃ D : ℕ,
    max (400*3202) (12800*K)<D ∧ ∃ T : ℕ, ∀ t : ℕ, T≤t →
    ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) (S : Finset V),
    hadwigerNumber G<t → (2*D+4*32768+5)*t+2<ell G S →
    (∃ J⊆S, ∃ H⊆S, Disjoint J H ∧ KConnectedOn G J (K*t) ∧
      KConnectedOn G H (K*t) ∧ (J.card:ℝ)≤(t:ℝ)^(53/50:ℝ) ∧
      (H.card:ℝ)≤(t:ℝ)^(53/50:ℝ)) ∨ FractionalObstruction G := by
  sorry

end LinearListHadwiger.Stage

end OAI
end
