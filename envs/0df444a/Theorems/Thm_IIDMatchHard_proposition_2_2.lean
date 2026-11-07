-- Prove2me | Theorems.Thm_IIDMatchHard_proposition_2_2
-- name    : IIDMatchHard.proposition_2_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T08:05:21.8797+00:00
-- url     : https://prove2.me/theorems/33b821b7-b5e8-4f30-8daf-16001d95bc82
-- title:
--   Proposition 2.2 — greedy policies dominate every deterministic policy
-- statement:
--   For every deterministic online policy $\pi$ there is a deterministic **greedy** policy $\pi'$, one that matches an arrival whenever it has a free neighbor, such that on every sequence of types
--   $$M_{\pi'}(\ell)\ \ge\ M_\pi(\ell)\qquad\text{for every }\ell\ge0.$$
--
--   The statement allows arbitrary offline and type sets and history-dependent neighbor sets $N(h,y)$, so it applies both to unweighted matching and to the adjusted Poisson model, where a blocked arrival is an arrival with no neighbors. It lets the analysis restrict to greedy policies.
--
--   Differences from the source:
--   - generalization: an unweighted instance with finite vertex and type sets and fixed neighbor sets → any vertex and type sets and history-dependent neighbor sets N h y; reason: the case N h y = nbr y is the paper statement; App. B.8 applies it to the adjusted model with blocked arrivals as arrivals without neighbors
--   - encoding: a deterministic policy deciding from the earlier arrivals and the matching history → a function of the earlier types, the matched set and the current type; a proposal that is not a free neighbor is a rejection; reason: the matched set is a function of the earlier types for a deterministic policy; same class of policies
--   - encoding: greedy: matches whenever there is a free neighbor → the condition is imposed at the states the policy reaches on its own run; reason: other states never occur
--   - encoding: M_π(ℓ) on a sequence of types → numMatches on the first ℓ entries of a finite list; reason: Lean convention; same quantity
-- source:
--   Teng, Yang, Computational Hardness of Online Stochastic Matching (manuscript of Nov. 3, 2026, sha256 f0193d92…), Proposition 2.2, p.4 (PDF p.5)

import Definitions.Def_IIDMatchHard_Model

set_option autoImplicit false

namespace IIDMatchHard

/-- **Proposition 2.2 (Greedy policies).** For every deterministic policy `π` there is a
deterministic greedy policy `π'` such that, on every sequence of types, `M_π'(ℓ) ≥ M_π(ℓ)` for
every `ℓ ≥ 0`. Teng, Yang, *Computational Hardness of Online Stochastic Matching* (manuscript of Nov. 3, 2026,
sha256 f0193d92…), Proposition 2.2, p.4 (PDF p.5).

**Formalization Note.** Stated for arbitrary offline and type sets and for **history-dependent**
neighbor sets `N h y` (the neighbor set of an arrival of type `y` after the types `h`), which
covers the unweighted model of §2.1 (`N = static nbr`) and the adjusted Poisson model, where "a
blocked arrival counts as an arrival of a type without neighbors" (App. B.8, p.21). `M_π(ℓ)` on
the sequence `ys` is `numMatches N π (ys.take ℓ)`. -/
theorem proposition_2_2 {U Y : Type*} [DecidableEq U] (N : List Y → Y → Finset U)
    (π : Policy U Y) :
    ∃ π' : Policy U Y, IsGreedy N π' ∧
      ∀ (ys : List Y) (ℓ : ℕ), numMatches N π (ys.take ℓ) ≤ numMatches N π' (ys.take ℓ) := by sorry

end IIDMatchHard
