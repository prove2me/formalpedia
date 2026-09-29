-- Prove2me | Theorems.Thm_OnlinePrimalDual_MTS_standard_to_new
-- name    : OnlinePrimalDual.MTS.standard_to_new
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-21T05:43:34.165428+00:00
-- url     : https://prove2.me/theorems/a068cc6e-1504-49f4-8125-c647adde9fcb
-- title:
--   Lemma 6.1 — standard-model solutions transform into new-model solutions at cost ≤2× (goal)
-- statement:
--   Any standard-model solution (given by its runs `s`, `w`) transforms into a new-model
--   solution whose cost is at most twice `costStandard ws s w`.
-- source:
--   Buchbinder & Naor, The Design of Competitive Online Algorithms via a Primal-Dual Approach, FnT TCS 2009, p. 144, Lemma 6.1

import Mathlib
import Definitions.Def_OnlinePrimalDual_MTS_WeightedStar
import Definitions.Def_OnlinePrimalDual_MTS_WeightedStar_d
import Definitions.Def_OnlinePrimalDual_MTS_costStandard

namespace OnlinePrimalDual.MTS

/-- **Lemma 6.1** (p. 144, PDF p. 55) — the goal of this mission. Any standard-model solution,
given by its `k` runs (`s`, the state of each run; `w`, each run's service cost, matching
`costStandard`'s own decomposition), transforms into a new-model solution with cost at most
twice `costStandard`: the book's own proof (p. 144-145) bounds, run by run, the corresponding
segment of the constructed solution `S′` by `Wᵢ + 2d(sᵢ)` ("its cost is at most `Wᵢ + 2d(sᵢ)`,
which is at most twice the cost incurred by solution `S`"). `w′ i` is this segment's new-model
cost; `∑w′ i ≤ 2·costStandard` is the book's own final displayed bound,
`∑(Wᵢ+2d(sᵢ)) ≤ 2∑(Wᵢ+d(sᵢ))`, using `w i ≥ 0`.

Non-vacuity guard, revised per `CHANGES_REQUESTED.md`'s moderation item (2026-09-21): a *universal*
per-index lower bound `∀ i, d(sᵢ) ≤ w′ i` is **not** something the book's proof establishes — `S′`
only provably visits `sᵢ` for at least one full phase when it does not skip past `sᵢ` (it jumps to
wherever `S` currently is when its own phase ends, p. 144, so it can skip states entirely), and the
book's two supporting claims are explicitly conditional on `S′` visiting `sᵢ` during
`[tᵢ₋₁,tᵢ]`. What the construction *does* guarantee unconditionally, from "at time `t=0`, `S′` is
in the same state as `S`" (p. 144, the base case, no skip is possible before any transition has
happened), is that the very first run is visited: `hk : 0 < k` (a nonempty run sequence — the case
`k = 0` is the empty/no-op solution, not the content of the lemma) gives
`d(s ⟨0,hk⟩) ≤ w′ ⟨0,hk⟩`. This rules out the vacuous witness `w′ := 0` whenever `d (s ⟨0,hk⟩) > 0`
without asserting the unproved universal statement; it is the strongest per-index guard the book's
own base case licenses. The "In particular, `OPTₙ(σ̄) ≤ 2·OPTₒ(σ̄)`" corollary follows by taking
`(s,w)` to realize `OPTₒ` and noting the constructed `w′` witnesses a new-model-feasible cost
`≤ 2·OPTₒ`, hence `OPTₙ ≤ 2·OPTₒ`; not separately restated here since it is an immediate corollary
of this existential, not a further fact to prove. -/
theorem standard_to_new {V : Type*} {k : ℕ} (hk : 0 < k) (ws : WeightedStar V)
    (s : Fin k → V) (w : Fin k → ℝ) (hw_nonneg : ∀ i, 0 ≤ w i) :
    ∃ w' : Fin k → ℝ, ws.d (s ⟨0, hk⟩) ≤ w' ⟨0, hk⟩ ∧
      (∀ i, w' i ≤ w i + 2 * ws.d (s i)) ∧
      ∑ i, w' i ≤ 2 * costStandard ws s w := by sorry

end OnlinePrimalDual.MTS
