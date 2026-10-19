-- Prove2me | Theorems.Thm_OAI_LinearListHadwiger_Recursion_three_regions
-- name    : OAI.LinearListHadwiger.Recursion.three_regions
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-19T02:46:44.115979+00:00
-- url     : https://prove2.me/theorems/3c9f43ce-8178-486f-bda3-88c8a7e7e7b7
-- title:
--   Three disjoint highly connected regions of large list chromatic number, or a fractional obstruction (OpenAI, linear list Hadwiger)
-- statement:
--   There are constants $S \ge 1$ and $T \ge 1$ with the following property. Let $t \ge T$, let $G$ be a finite graph with $h(G) < t$, let $H$ be a vertex set, and let $k \ge 1$ and $R$ be natural numbers. Write $\ell(H)$ = `ell G H` for the list chromatic number of $G[H]$. Assume
--   $$3St \le \ell(H) \quad\text{and}\quad R + 6k + 2St < \ell(H).$$
--   Then one of two things holds:
--   - there are three pairwise disjoint subsets $J_0, J_1, J_2 \subseteq H$, each $k$-connected (`KConnectedOn G (J d) k`) and each with $\ell(J_d) > R$;
--   - $G$ has a fractional obstruction.
--
--   `ell`, `KConnectedOn` and `FractionalObstruction` come from the definitions bundle `OAIQWLLH000` of this split, and `hadwigerNumber` comes from the published bundle `Def_ListHadwiger`. `KConnectedOn G J k` means that $|J| > k$ and that $G[J \setminus Z]$ is connected for every $Z \subseteq J$ with $|Z| < k$. The carver publishes this lemma as an intermediate statement so that each proof fits the platform's verifier.
--
--   Lean: `OAI.LinearListHadwiger.Recursion.three_regions`, OpenAI's theorem of that name in `lean/OAI/Combinatorics/ListHadwiger/RecursiveDistricts.lean`.
-- source:
--   OpenAI, A linear list-coloring bound in terms of the Hadwiger number, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 157; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-linear-list-coloring-bound-in-terms-of-the-Hadwiger-number-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/ListHadwiger/RecursiveDistricts.lean (declaration OAI.LinearListHadwiger.Recursion.three_regions)

import Mathlib
import Definitions.Def_ListHadwiger
import Definitions.Def_OAIQWLLH000

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace LinearListHadwiger.Recursion
open Finset Stage SmallList
attribute [local instance] Classical.propDecidable
variable {V : Type} [Fintype V] [DecidableEq V]

theorem three_regions : ∃ S : ℕ, 1≤S ∧ ∃ T : ℕ, 1≤T ∧
    ∀ t : ℕ, T≤t → ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (H : Finset V) (k R : ℕ), 1≤k → hadwigerNumber G<t →
    3*S*t≤ell G H → R+6*k+2*S*t<ell G H →
    (∃ J : Fin 3 → Finset V,
      (∀ d, J d⊆H) ∧ (∀ d e, d≠e → Disjoint (J d) (J e)) ∧
      (∀ d, KConnectedOn G (J d) k) ∧ (∀ d, R<ell G (J d))) ∨ FractionalObstruction G := by
  sorry

end LinearListHadwiger.Recursion

end OAI
end
