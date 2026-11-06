-- Prove2me | Theorems.Thm_FullPathSCC_prop_A_1
-- name    : FullPathSCC.prop_A_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-05T20:22:21.826809+00:00
-- url     : https://prove2.me/theorems/a817408f-d2fb-41cf-a324-36e79bb01869
-- title:
--   Proposition A.1 (A.1) — the full-path accumulated preference satisfies $V_t=u(c_t)+\mathcal E^{FP}_t(\beta V_{t+1})$
-- statement:
--   Let $k>0$, $0<\beta<1$ and $N\in\mathbb N$. On a probability space with a filtration $(\mathcal F_t)$, write $E_t$ for the conditional expectation given $\mathcal F_t$, let $u_s=u(c_s)$, $s\le N$, be real random variables with $u_s$ $\mathcal F_s$-measurable, and suppose that $e^{-k\beta^t\sum_{s=t}^N\beta^{s-t}u_s}$ is integrable for every $t\le N$. Put
--
--   $$
--   V_t=-\frac1{k\beta^t}\ln E_t\Bigl[e^{-k\beta^t\sum_{s=t}^N\beta^{s-t}u_s}\Bigr],\qquad \mathcal E^{FP}_t(X)=-\frac1{k\beta^t}\ln E_t\bigl[e^{-k\beta^tX}\bigr].
--   $$
--
--   Then for every $0\le t<N$, almost surely,
--
--   $$
--   V_t=u_t+\mathcal E^{FP}_t(\beta V_{t+1}).
--   $$
--
--   This is the second equality of (6): the path form of the preference and its recursive form agree.
--
--   Differences from the source:
--   - reading: $t\ge0$ → $0\le t<N$; reason: $V_{t+1}$ exists only for $t+1\le N$
--   - generalization: $u(c_s)$ for a consumption stream $c_s$ and a utility function $u$ → any real process $u_s$ with $u_s$ known at time $s$; reason: $u(c_s)$ is such a process, because the proof (A.2) takes $e^{-k\beta^tu(c_t)}$ out of $E_t$ as known at time $t$
--   - encoding: the operators $E_t$ "conditional on the events that have unfolded up to and including time $t$" (§2, p.7587), "the event filtration" (p.7600) → conditional expectation given $\mathcal F_t$ for a filtration on a probability space, and the equality holds almost surely; reason: this is what the operators are, and conditional expectations are defined up to null sets
--   - encoding: the expectations in (6) are taken to exist → integrability of $e^{-k\beta^t\sum_{s=t}^N\beta^{s-t}u_s}$ for $t\le N$; reason: this only excludes cases where $E_t$ of (6) is undefined as a real number
--   - generalization: a horizon $n>0$ (§2, p.7587) → $N\ge0$; reason: $N=0$ only adds a vacuous case
-- source:
--   Zhao, Basu, Lontzek & Schmedders, The Social Cost of Carbon When We Wish for Full-Path Robustness, Management Science 69(12) (2023), doi:10.1287/mnsc.2023.4736, Proposition A.1, (A.1) and (A.2), p.7600; (6), p.7589

import Mathlib
import Definitions.Def_FullPathSCC_continuationUtility

namespace FullPathSCC

open MeasureTheory

/-- **Proposition A.1** (Management Science 69(12) (2023), p.7600, (A.1), proof (A.2); Equality (6),
p.7589): `V_t = u(c_t) + ℰ^FP_t(βV_{t+1})`, for the full-path accumulated preference
`V_t = −(1/(kβ^t)) ln E_t[e^{−kβ^t Σ_{s=t}^N β^{s−t} u(c_s)}]` of a consumption stream, with `k > 0`
and `0 < β < 1` (§2, p.7587).

**Formalization Note** The page's setting is §2: an abstract underlying randomness with the
expectation operators `E_t` "conditional on the events that have unfolded up to and including
time `t`" (p.7587). So `E_t` is the conditional expectation given `ℱ t` for a filtration `ℱ` on a
probability space, `u s` is the random variable `u(c_s)`, known at time `s`, and the equality holds
almost surely. `hint` says that the expectations in (6) exist. Since `V_{t+1}` is only defined for
`t + 1 ≤ N`, the recursion is stated for `t < N`. -/
theorem prop_A_1 {Ω : Type*} {m0 : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    (ℱ : Filtration ℕ m0) (k β : ℝ) (hk : 0 < k) (hβ0 : 0 < β) (hβ1 : β < 1) (N : ℕ)
    (u : ℕ → Ω → ℝ) (hu : ∀ s ≤ N, StronglyMeasurable[ℱ s] (u s))
    (hint : ∀ t ≤ N, Integrable
      (fun ω => Real.exp (-(k * β ^ t) * ∑ s ∈ Finset.Icc t N, β ^ (s - t) * u s ω)) P) :
    ∀ t < N, continuationUtility P ℱ k β N u t =ᵐ[P] fun ω =>
      u t ω + fullPathCE P ℱ k β t (fun ω' => β * continuationUtility P ℱ k β N u (t + 1) ω') ω := by sorry

end FullPathSCC
