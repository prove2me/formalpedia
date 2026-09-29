-- Prove2me | Theorems.Thm_OnlinePrimalDual_BoundedAllocation_theorem13_1
-- name    : OnlinePrimalDual.BoundedAllocation.theorem13_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-21T06:07:20.757416+00:00
-- url     : https://prove2.me/theorems/4e7bbdc7-702c-4a46-9ece-4cc674afdc12
-- title:
--   Generic per-item weak-duality template for the C(d) ratio (goal; relabeled per moderation)
-- statement:
--   Relabeled per moderation (2026-09-21): given a fractional allocation yAlg, per-item changes
--   ΔX, ΔY satisfying the book's core inequality ΔX(j) ≤ (1/C(d))ΔY(j), ΔY equal to yAlg's own
--   per-item dual profit, and ΔX's total dominating any feasible allocation's value (weak
--   duality, not tied to the book's own allocX/potential machinery), the resulting ratio
--   inequality holds: for any feasible comparison allocation y'', C(d)·packingValue(y'') ≤
--   packingValue(yAlg). This is the shared weak-duality skeleton Theorem 13.1's own proof is
--   built from, not (yet) a formalization of the theorem's own claim about the specific
--   level-based algorithm — the previous version's extra hypotheses tying this to allocX/t were
--   dead (unused by the proof) and have been removed rather than left as a false impression of
--   connection; see STATUS.md for the follow-on this leaves open.
-- source:
--   Buchbinder & Naor, The Design of Competitive Online Algorithms via a Primal-Dual Approach, FnT TCS 2009, p. 240-244, Theorem 13.1

import Mathlib
import Definitions.Def_OnlinePrimalDual_BoundedAllocation_AllocationInstance
import Definitions.Def_OnlinePrimalDual_BoundedAllocation_competitiveRatio
import Definitions.Def_OnlinePrimalDual_BoundedAllocation_packingFeasible
import Definitions.Def_OnlinePrimalDual_BoundedAllocation_packingValue

namespace OnlinePrimalDual.BoundedAllocation

/-- **Generic per-item weak-duality template for the bounded-allocation ratio**, built from the
ingredients Theorem 13.1's proof combines (p. 240-244, PDF p. 151-155) — **relabeled per
`CHANGES_REQUESTED.md`'s required fix, option (b) (moderation, 2026-09-21)**: the previous version
of this item additionally carried `t`, `ht_le`, and `hX_def` (tying the abstract `∑ΔX` to
`allocX`/the potential function `f_d`), but those hypotheses played no role in deriving the
conclusion from `hΔY_def`, `hinvariant` and `hX_ge` alone — the theorem was a generic
weak-duality corollary satisfiable by *any* allocation for which some abstract `ΔX`/`ΔY` pair can
be found, not a formalization tied to the book's actual level-based algorithm or its potential
function. Wiring `hX_def` in for real (option (a): deriving `hX_ge` as a consequence of LP weak
duality applied to the *same* primal solution `allocX inst.d t` builds, and accounting for Fig.
13.1's `z(j)` terms) is a substantially larger undertaking left for a future pass — flagged in
`STATUS.md`. This item is honestly relabeled as what it actually proves: given `ΔX`, `ΔY : J → ℝ`
satisfying the book's own per-item invariant `ΔX(j) ≤ (1/C(d))ΔY(j)` (`hinvariant`, established in
the book by a case analysis on `f_d` across levels, p. 241-244, not reproduced here), `ΔY` equal to
`yAlg`'s own per-item dual profit (`hΔY_def`), and `∑ΔX` dominating any feasible allocation's
value (`hX_ge`, weak duality against an *unconnected* `∑ΔX`, not `allocX inst.d t`'s own cost),
the resulting ratio inequality holds. `allocX`/`potential`/`geomSeq`, this mission's own
formalizations of the book's actual algorithm, are not used by this item's statement or proof —
they remain milestones on their own, not inputs here. -/
theorem theorem13_1 {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I]
    (inst : AllocationInstance I J) (yAlg : I → J → ℝ) (hyAlg_feasible : packingFeasible inst yAlg)
    (ΔX ΔY : J → ℝ) (hΔY_def : ∀ j, ΔY j = ∑ i ∈ inst.S j, inst.b j * yAlg i j)
    (hinvariant : ∀ j, ΔX j ≤ (1 / competitiveRatio inst.d) * ΔY j)
    (hX_ge : ∀ y'', packingFeasible inst y'' → packingValue inst y'' ≤ ∑ j, ΔX j) :
    ∀ y'' : I → J → ℝ, packingFeasible inst y'' →
      competitiveRatio inst.d * packingValue inst y'' ≤ packingValue inst yAlg := by sorry

end OnlinePrimalDual.BoundedAllocation
