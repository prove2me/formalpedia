-- Prove2me | Theorems.Thm_MultiServerAppt_waiting_time_hitting_time
-- name    : MultiServerAppt.waiting_time_hitting_time
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T19:00:09.120528+00:00
-- url     : https://prove2.me/theorems/6d63de28-6ee8-4e1e-8855-6d278bc30ccb
-- title:
--   Eq. (5) — the waiting time as a hitting time
-- statement:
--   Let $s\ge 1$, let $c$ be any client, and let $b_d\ge 0$ be any service times. With $Y_c$ the number of the first $c$ clients present,
--
--   $$W_c=\inf\{t\ge 0: Y_c(t)\le s\}=\inf\{t\ge 0: Y_{c-1}(t+x_c)<s\}.$$
--
--   A client's service starts at the moment when a server comes available to it. This relates the waiting time to the process $Y$ that the phase-type recursion tracks.
--
--   **Formalization Note** For $c\le s$ both sides are $0$: $W_c=0$ and both sets are $[0,\infty)$.
--
--   Differences from the source:
--   - generalization: client i with the random service times of the model → every client c, every deterministic b ≥ 0 and every real x; reason: the identity is pathwise; the source's paths are instances, and for c ≤ s both sides are 0
-- source:
--   Kuiper–Lee, Appointment Scheduling for Multiple Servers, SSRN 3975471, Eq. (5), p.10

import Mathlib
import Definitions.Def_MultiServerAppt_W
import Definitions.Def_MultiServerAppt_Y

namespace MultiServerAppt

/-- Eq. (5): for every client `c`, the waiting time is the hitting time of `{Y_c ≤ s}`, and also that
of `{Y_{c-1}(· + x_c) < s}`. Deterministic, for any service times `b ≥ 0`. Kuiper–Lee, Appointment
Scheduling for Multiple Servers, SSRN 3975471, Eq. (5), p.10.

**Formalization Note** For `c ≤ s` both sides are `0` (`W c = 0`, and both sets are `[0, ∞)`), so no
restriction on `c` is needed. The sets are subsets of `[0, ∞)` that contain `W c`, so the `sInf` are
minima, not junk values. -/
theorem waiting_time_hitting_time (s c : ℕ) (x b : ℕ → ℝ) (hs : 1 ≤ s)
    (hb : ∀ d, 0 ≤ b d) :
    W s x b c = sInf {t : ℝ | 0 ≤ t ∧ Y s x b c t ≤ s} ∧
    W s x b c = sInf {t : ℝ | 0 ≤ t ∧ Y s x b (c - 1) (t + x c) < s} := by sorry

end MultiServerAppt
