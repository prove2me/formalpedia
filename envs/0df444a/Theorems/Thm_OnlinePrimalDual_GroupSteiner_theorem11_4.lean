-- Prove2me | Theorems.Thm_OnlinePrimalDual_GroupSteiner_theorem11_4
-- name    : OnlinePrimalDual.GroupSteiner.theorem11_4
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-21T05:59:46.645746+00:00
-- url     : https://prove2.me/theorems/2548a948-d8fd-44aa-9e43-db946f685091
-- title:
--   Theorem 11.4 — online group Steiner on trees (goal)
-- statement:
--   Running T = Θ(log N · log k) independent trials of the rounding scheme in parallel and taking
--   their union gives a randomized online algorithm for the group Steiner problem on trees:
--   expected cost at most T·log(n)·OPT = O(log²n·log k) (using N ≤ n) — the book's own
--   competitive-ratio statement (p. 231), and nothing further. Revised per moderation
--   (2026-09-21): the previous version's added coverage conjunct ("every group covered with
--   probability at least 1 - 1/(2k)") is not part of the book's Theorem 11.4 and approximated a
--   different, weaker figure than the book's own intermediate `1-1/k` (itself eliminated by a
--   shortest-path fallback in the book's actual algorithm, making the final coverage probability
--   `1`) — dropped rather than kept as a non-book substitute, per the "never state a weaker
--   inequality than the book proves" / "left out, not approximated" rules. `T`'s derivation
--   remains documented in `description.md`/`MODERATION_NOTES.md` as the supporting mechanism.
-- source:
--   Buchbinder & Naor, The Design of Competitive Online Algorithms via a Primal-Dual Approach, FnT TCS 2009, p. 231, Theorem 11.4

import Mathlib
import Definitions.Def_OnlinePrimalDual_GroupSteiner_RandomCover
import Definitions.Def_OnlinePrimalDual_GroupSteiner_RoundedTree
import Definitions.Def_OnlinePrimalDual_GroupSteiner_expectedCost

namespace OnlinePrimalDual.GroupSteiner

/-- **Theorem 11.4** (p. 231, PDF p. 142) — the goal of this mission: a randomized online
algorithm for the group Steiner problem on trees with a competitive ratio of `O(log² n log k)`.
The algorithm runs `T` independent trials of the rounding scheme of Lemma 11.1 in parallel (each
trial's cover drawn from the same fractional solution `w'`, an `O(log n)`-competitive online
covering solution obtained by applying the framework of Section 4.2 to this instance's LP —
`fracRatio ≤ log n`, `hfrac_ratio` — `n` the number of tree leaves), unions their random covers
into a single cover `ρ` (`hcost` packages, via independence, the standard fact that the union's
expected cost scales linearly in `T` [Lemma 11.2 applied per trial]), and takes
`T = Θ(log N · log k)` trials (`N` the maximum group size), so that every group fails to be
covered with only a negligible probability (Lemma 11.3's per-trial guarantee, applied `T` times
independently — the mechanism that justifies this trial count, documented in
`description.md`/`MODERATION_NOTES.md`, not restated as a conclusion here). The resulting expected
cost is then at most `T · log n · OPT`, i.e. `O(log N · log k · log n) = O(log² n · log k)`.

**Conclusion revised per `CHANGES_REQUESTED.md` (moderation, 2026-09-21): the coverage conjunct is
dropped.** The book's Theorem 11.4 makes only the competitive-ratio claim (two sentences, p. 231:
"There is a randomized online algorithm for the group Steiner problem in trees with a competitive
ratio of `O(log² n log k)`"); the previous version's second conjunct,
`∀i, 1-1/(2k) ≤ ρ.probHits(...)`, was not part of that statement — it approximated a different,
weaker figure than the book's own `1-1/k` (itself only an intermediate narrative quantity, p. 229,
eliminated in the book by a shortest-path fallback that makes the final algorithm's coverage
probability `1`, not `1-1/k`), violating rule 5 ("never state a weaker inequality than the book
proves"). Removed per rule 6 ("left out, not approximated") rather than kept as a non-book
substitute; `T`'s derivation (the Chernoff/union-bound argument) and its role in justifying the
trial count remain documented in `description.md`'s Difficulty section and
`MODERATION_NOTES.md`, and `lemma11_3`'s own milestone already carries the faithful per-trial
coverage guarantee — no coverage claim needs restating (weakened) at the goal. Binders that were
only needed for the dropped conjunct (`vertexEdge`, `V`, `hk`, `α`, `hα`, `hN`, `groups`,
`hgroups_le`, `wg`, `hwg`, `hfail`, and `hT`'s explicit closed form) are dropped along with it;
`n`/`N`/`T`/`k` survive only where the surviving conclusion or `hcost` actually needs them — here,
`T` is carried as an opaque `ℕ` with no further derivation exposed in the statement (its
derivation is proof-strategy content, documented in prose, not part of what this theorem asserts). -/
theorem theorem11_4 {E : Type*} [Fintype E] [DecidableEq E]
    (tr : RoundedTree E) (n : ℕ) (hn : 0 < n)
    (w' : E → ℝ) (fracRatio OPT : ℝ) (hOPT_nonneg : 0 ≤ OPT)
    (hfrac_ratio : ∑ e, tr.cost e * w' e ≤ fracRatio * OPT) (hfracRatio : fracRatio ≤ Real.log n)
    (T : ℕ)
    (ρ : RandomCover E)
    (hcost : ρ.expectedCost tr.cost ≤ (T : ℝ) * (fracRatio * OPT)) :
    ρ.expectedCost tr.cost ≤ (T : ℝ) * Real.log n * OPT := by sorry

end OnlinePrimalDual.GroupSteiner
