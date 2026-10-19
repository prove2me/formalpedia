-- Prove2me | Theorems.Thm_OAI_LinearListHadwiger_Footprint_History_list_loss_or_obstruction
-- name    : OAI.LinearListHadwiger.Footprint.History.list_loss_or_obstruction
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-19T02:46:38.534579+00:00
-- url     : https://prove2.me/theorems/e1669e37-e80c-4b56-92b2-5e5121472b89
-- title:
--   Deleting the footprint of a stage history costs O(t) list colours, or there is a fractional obstruction (OpenAI, linear list Hadwiger)
-- statement:
--   There is a $t_0$ such that the following holds for every $t \ge t_0$ and every finite graph $G$ with $h(G) < t$. Let $H$ be a stage history of $G$ (`History G t`) with at most `rounds t` $= \lceil (\log t)^2 \rceil$ stages. Then either
--   $$\chi_{\mathrm{list}}(G) \le \chi_{\mathrm{list}}\bigl(G - \mathrm{footprint}_{H}(q)\bigr) + (4\cdot 32768 + 6\cdot 3202 + 25)\,t,$$
--   or $G$ has a fractional obstruction (`FractionalObstruction G`). Here $\mathrm{footprint}_H(q)$ is the footprint of the history after its last stage $q$ = `H.q`.
--
--   `History`, `rounds` and `FractionalObstruction` come from the definitions bundle `OAIQWLLH000` of this split. `listChromaticNumber` and `hadwigerNumber` come from the published bundle `Def_ListHadwiger`. The carver publishes this lemma as an intermediate statement so that each proof fits the platform's verifier.
--
--   Lean: `OAI.LinearListHadwiger.Footprint.History.list_loss_or_obstruction`, OpenAI's theorem of that name in `lean/OAI/Combinatorics/ListHadwiger/HistoryBounds.lean`.
-- source:
--   OpenAI, A linear list-coloring bound in terms of the Hadwiger number, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 157; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-linear-list-coloring-bound-in-terms-of-the-Hadwiger-number-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/ListHadwiger/HistoryBounds.lean (declaration OAI.LinearListHadwiger.Footprint.History.list_loss_or_obstruction)

import Mathlib
import Definitions.Def_ListHadwiger
import Definitions.Def_OAIQWLLH000

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace LinearListHadwiger.Footprint.History
open Finset SmallList

theorem list_loss_or_obstruction : ∃ t₀ : ℕ, ∀ t : ℕ, t₀ ≤ t →
    ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) (H : History G t),
    hadwigerNumber G < t → H.q ≤ rounds t →
    listChromaticNumber G ≤ listChromaticNumber (G.induce (↑(univ\H.footprint H.q):Set V)) +
      (4*32768+6*3202+25)*t ∨ FractionalObstruction G := by
  sorry

end LinearListHadwiger.Footprint.History

end OAI
end
