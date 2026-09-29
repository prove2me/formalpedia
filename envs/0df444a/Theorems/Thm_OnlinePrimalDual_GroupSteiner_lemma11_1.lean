-- Prove2me | Theorems.Thm_OnlinePrimalDual_GroupSteiner_lemma11_1
-- name    : OnlinePrimalDual.GroupSteiner.lemma11_1
-- status  : Disproved
-- author  : @mikedeng1
-- created : 2026-09-21T05:58:04.730778+00:00
-- url     : https://prove2.me/theorems/5771b985-172f-445d-a72e-63fd06f966fd
-- title:
--   Lemma 11.1 — marginal probability of the rounding algorithm's random cover
-- statement:
--   For a single iteration augmenting weights from `w` to `w' = w + δ` (`δ ≥ 0`), the rounding
--   algorithm's three-case update rule (deterministic add when `w'_e > 1`; a single coin flip when
--   the parent's presence in `C` is already certain; a coin flip conditional on the parent being
--   in `C` otherwise) yields, at the end of the iteration, `ℙ[e ∈ C] = w'_e` for every edge with
--   `w'_e ≤ 1` (revised per moderation, 2026-09-21: restricted from an unconditional claim, which
--   is false once `w'_e` exceeds `1` and is no longer a probability), and `ℙ[e ∈ C] = 1` whenever
--   `w_e > 1`.
-- source:
--   Buchbinder & Naor, The Design of Competitive Online Algorithms via a Primal-Dual Approach, FnT TCS 2009, p. 230, Lemma 11.1

import Mathlib
import Definitions.Def_OnlinePrimalDual_GroupSteiner_RandomCover
import Definitions.Def_OnlinePrimalDual_GroupSteiner_marg
import Definitions.Def_OnlinePrimalDual_GroupSteiner_condProb
import Definitions.Def_OnlinePrimalDual_GroupSteiner_RoundedTree

namespace OnlinePrimalDual.GroupSteiner

/-- **Lemma 11.1** (p. 230, PDF p. 141). For a single iteration in which the fractional weight of
edges is augmented from `w` to `w' = w + δ` (`δ e ≥ 0` the increment; edges with `δ e = 0` are
untouched this iteration), the rounding algorithm (Algorithm box, p. 229-230) processes every
edge `e` with `δ e > 0`, in a topological order starting from the root, deciding whether to add
it to the random cover (represented, at the end of the iteration, by `ρ : RandomCover E`) by:
adding it deterministically if `w' e > 1` (`hrule1`, first bullet); otherwise, if `e` is incident
to the root or `w'_{parent e} > 1` — so the parent's own presence in `C` is already certain —
flipping a coin that succeeds with probability `δ e / (1 - w e)`, which combined with the already
certain event gives the resulting marginal `w e + (1 - w e) · δ e / (1 - w e) = w' e` exactly
(`hrule2`, second bullet); otherwise (`e` not incident to the root and `w'_{parent e} ≤ 1`),
adding it with conditional probability `δ e / (w'_{parent e} - w e)` given `parent e ∈ C`
(`hrule3`, third bullet — the genuinely recursive case, needing the parent's own marginal,
established one level up the tree by the same lemma). `hprev` is the inductive hypothesis
inherited from the previous iteration: edges untouched this iteration keep their previous
marginal probability. The source states this lemma without proof, citing the offline analysis of
Garg, Konjevod & Ravi [56]; the induction on the topological order is not reproduced in this
survey (`STATUS.md`).

**First conjunct revised per `CHANGES_REQUESTED.md` (moderation, 2026-09-21)**: restricted to
`w' e ≤ 1`, matching the book's own implicit reading — clause (a), "the probability that `e ∈ C`
is `w'_e`," is only meaningful when `w'_e` is itself a valid probability (`≤ 1`); clause (b) is
precisely the override for `w'_e > 1`. The prior unconditional `∀ e, ρ.marg e = w' e` was false: a
single root-incident edge `e0` with `w e0 = 0`, `δ e0 = 3` (`w' e0 = 3`) and `ρ` a point mass on
`{e0}` satisfies every hypothesis (`hrule1` by choice of `ρ`; `hrule2`/`hrule3` vacuous since their
premise `w' e ≤ 1` fails; `hprev` vacuous since `δ e0 ≠ 0`) while `ρ.marg e0 = 1 ≠ 3 = w' e0`.
Restricting the first conjunct to `w' e ≤ 1` makes it and `hrule1`'s case (`w' e > 1`) address
disjoint edges, closing the gap. -/
theorem lemma11_1 {E : Type*} [Fintype E] [DecidableEq E] (tr : RoundedTree E) (ρ : RandomCover E)
    (w w' δ : E → ℝ) (hδ_def : ∀ e, w' e = w e + δ e) (hδ_nonneg : ∀ e, 0 ≤ δ e)
    (hprev : ∀ e, δ e = 0 → ρ.marg e = w e)
    (hrule1 : ∀ e, δ e > 0 → w' e > 1 → ρ.marg e = 1)
    (hrule2 : ∀ e, δ e > 0 → w' e ≤ 1 →
      (tr.parent e = none ∨ ∃ p, tr.parent e = some p ∧ w' p > 1) →
      ρ.marg e = w' e)
    (hrule3 : ∀ e p, δ e > 0 → w' e ≤ 1 → tr.parent e = some p → w' p ≤ 1 →
      ρ.condProb e p = δ e / (w' p - w e)) :
    (∀ e, w' e ≤ 1 → ρ.marg e = w' e) ∧ (∀ e, w e > 1 → ρ.marg e = 1) := by sorry

end OnlinePrimalDual.GroupSteiner
