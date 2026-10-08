-- Prove2me | Theorems.Thm_LindleyQueue_Stability_lindley_theorem
-- name    : LindleyQueue.Stability.lindley_theorem
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T12:38:37.975083+00:00
-- url     : https://prove2.me/theorems/9a490460-284a-43ad-b033-e6bb264a079b
-- title:
--   Lindley's theorem — the waiting-time d.f. has a proper limit iff $\mathscr{E}(u) < 0$ or $u = 0$ a.s.
-- statement:
--   Consider Lindley's single-server queue: interarrival times $t_r$ i.i.d. with finite mean, service times $s_r$ i.i.d. with finite mean, the two families independent (Assumptions 1–2), all times nonnegative. Let $u = s - t$, let $w_r$ be the waiting time of the $r$th customer, defined by $w_1 = 0$ and $w_{r+1} = \max(w_r + u_r, 0)$, and let $F_r(x) = p(w_r \le x)$.
--
--   **Theorem.**
--
--   1. As the number of customers increases, the waiting-time distribution function tends to a non-degenerate limit if and only if
--   $$
--   \mathscr{E}(u) < 0 \quad \text{or} \quad u = 0 \text{ certainly.}
--   $$
--   Here "tends to a non-degenerate limit" means: there is a probability distribution $\nu$ on $\mathbb R$ such that $F_r(x) \to \nu((-\infty, x])$ as $r \to \infty$ at every $x$ with $\nu(\{x\}) = 0$.
--   2. If $\mathscr{E}(u) \ge 0$ and $u$ is not almost surely $0$, then for every real $x$,
--   $$
--   \lim_{r \to \infty} p(w_r \le x) = 0.
--   $$
--
--   This is the stability criterion for the GI/G/1 queue: an equilibrium waiting-time distribution exists exactly when the mean service time is less than the mean interarrival time (apart from the deterministic case $s_r = t_r$), and otherwise the probability of waiting no more than any given time tends to zero.
--
--   **Formalization Note** "Non-degenerate" is read as *proper*: the limit is a probability distribution (no mass escapes to $+\infty$). It does not mean "not a point mass": when $u = 0$ a.s. every customer waits $0$ and the limit is the point mass at $0$, which the theorem counts as convergent. Convergence of distribution functions is the classical one, at the continuity points of the limit. "Certainly" is read as almost surely, for $u_1$ (all $u_r$ share its law). $\mathscr{E}(u)$ is the Bochner integral of the integrable `u 0`. Lean numbers customers from $0$ (`F r` is the paper's $F_{r+1}$), which does not affect limits.
-- source:
--   Lindley (Proc. Camb. Phil. Soc. 48, 1952), §4, THEOREM, p. 281

import Mathlib
import Definitions.Def_LindleyQueue_Stability_Model
open MeasureTheory ProbabilityTheory Filter Topology

namespace LindleyQueue.Stability

/-- Lindley's THEOREM (§4, p. 281). The waiting-time distribution functions `F r`
converge (at every continuity point of the limit) to the distribution function of a probability
measure on `ℝ` if and only if `𝓔(u) < 0` or `u = 0` almost surely; and if `𝓔(u) ≥ 0` and
`u` is not almost surely `0`, then `F r x → 0` for every `x`. -/
theorem lindley_theorem {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (Q : Input Ω P) :
    ((∃ ν : Measure ℝ, IsProbabilityMeasure ν ∧
        ∀ x : ℝ, ν {x} = 0 → Tendsto (fun r => Q.F r x) atTop (𝓝 (ν.real (Set.Iic x))))
      ↔ (∫ ω, Q.u 0 ω ∂P < 0 ∨ Q.u 0 =ᵐ[P] 0)) ∧
    (0 ≤ ∫ ω, Q.u 0 ω ∂P → ¬ (Q.u 0 =ᵐ[P] 0) →
      ∀ x : ℝ, Tendsto (fun r => Q.F r x) atTop (𝓝 0)) := by sorry

end LindleyQueue.Stability
