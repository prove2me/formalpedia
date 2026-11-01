-- Prove2me | Theorems.Thm_OfflineToOnline_proposition_1
-- name    : OfflineToOnline.proposition_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T11:34:59.705297+00:00
-- url     : https://prove2.me/theorems/966d8046-35e3-4ca1-a98e-8ba96edf322a
-- title:
--   Proposition 1 (corrected: satisfiability is only sufficient) — halfspace-, response-satisfiability and approachability
-- statement:
--   Let $(\mathcal X,\mathcal Y,\boldsymbol p)$ be a Blackwell game with $\mathcal X\subseteq\mathbb R^m$ and $\mathcal Y\subseteq\mathbb R^k$ compact and convex, $\mathcal X$ nonempty, and $\boldsymbol p$ biaffine on $\mathcal X\times\mathcal Y$. Let $S\subseteq\mathbb R^d$ be closed, convex and nonempty. Then:
--
--   1. $S$ is halfspace-satisfiable if and only if it is response-satisfiable;
--   2. $S$ is response-satisfiable if and only if it is approachable, i.e. $g(T)$-approachable in $\ell_\infty$ for some $g(T)\to0$;
--   3. if $S$ is satisfiable, then it is response-satisfiable (and hence approachable).
--
--   These are the structural criteria for approachability that the proof of Theorem 1 uses: the halfspace condition supplies the oracle that converts online linear optimization decisions into player 1 actions.
--
--   Differences from the source:
--   - correction: items 1 (satisfiable), 2 and 3 are all equivalent to approachability → items 2 and 3 are equivalent to each other and to approachability; item 1 implies them; reason: counterexample: X = Y = [0,1], p(x,y) = x − y, S = {0} is response-satisfiable and approachable, but no x has x − y = 0 for all y
--   - reading: the approachability condition (Definition 3) → for every ε > 0 there is T₀ such that for every T ≥ T₀ some player 1 strategy keeps the ℓ∞ distance of the average payoff to S at most ε against every sequence in Y; reason: Definition 3 with a vanishing rate g(T) → 0 (p.12)
--   - encoding: X, Y compact convex; S closed convex → additionally X nonempty and S nonempty; reason: Metric.infDist to ∅ is 0, and a game with no player 1 action has no strategy; neither case is a game of the paper
--   - encoding: player 1 and player 2 strategies; halfspaces H ⊇ S → deterministic full-history strategies against every sequence in Y; halfspaces {u : ⟨a,u⟩ ≤ c}; reason: against a deterministic strategy an adaptive player 2 is a sequence; standard halfspace form
-- source:
--   Niazadeh, Golrezaei, Wang, Susan & Badanidiyuru, Online Learning via Offline Greedy Algorithms: Applications in Market Design and Optimization, arXiv:2102.11050v4, Proposition 1, p.45

import Mathlib
import Definitions.Def_OfflineToOnline_IsBiaffineOn
import Definitions.Def_OfflineToOnline_IsSatisfiable
import Definitions.Def_OfflineToOnline_IsHalfspaceSatisfiable
import Definitions.Def_OfflineToOnline_IsResponseSatisfiable
import Definitions.Def_OfflineToOnline_fullHistoryPlay
import Definitions.Def_OfflineToOnline_IsApproachable

namespace OfflineToOnline

/-- **Proposition 1** (corrected: satisfiability is only sufficient). In the Blackwell game
`(X, Y, p)` with `X`, `Y` compact convex, `X` nonempty, `p` biaffine, and a closed convex nonempty
target set `S`:
(a) `S` is halfspace-satisfiable iff it is response-satisfiable;
(b) `S` is response-satisfiable iff it is approachable (Definition 3 with some `g(T) → 0`);
(c) if `S` is satisfiable, it is response-satisfiable (hence approachable).

Niazadeh, Golrezaei, Wang, Susan & Badanidiyuru, arXiv:2102.11050v4, Proposition 1, p.45.

Formalization Note: the page says all three conditions are equivalent to approachability. Item 1
(satisfiability) is not: for `X = Y = [0, 1]`, `p(x, y) = x − y`, `S = {0}`, the set `S` is
response-satisfiable and approachable, but no `x` has `x − y = 0` for all `y`. Distances are ℓ∞
(`Metric.infDist` in `Fin d → ℝ`). -/
theorem proposition_1 {m k d : ℕ} (X : Set (Fin m → ℝ)) (Y : Set (Fin k → ℝ))
    (p : (Fin m → ℝ) → (Fin k → ℝ) → (Fin d → ℝ)) (S : Set (Fin d → ℝ))
    (hXc : IsCompact X) (hXv : Convex ℝ X) (hXn : X.Nonempty) (hYc : IsCompact Y)
    (hYv : Convex ℝ Y) (hp : IsBiaffineOn X Y p) (hSc : IsClosed S) (hSv : Convex ℝ S)
    (hSn : S.Nonempty) :
    (IsHalfspaceSatisfiable X Y p S ↔ IsResponseSatisfiable X Y p S) ∧
      (IsResponseSatisfiable X Y p S ↔ IsApproachable p X Y S) ∧
      (IsSatisfiable X Y p S → IsResponseSatisfiable X Y p S) := by sorry

end OfflineToOnline
