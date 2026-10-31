-- Prove2me | Theorems.Thm_KashUpgrade_slice_decomposition
-- name    : KashUpgrade.slice_decomposition
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T03:26:05.320776+00:00
-- url     : https://prove2.me/theorems/b421342f-77b3-4fca-929b-756f56af9f46
-- title:
--   §4.2, p.14 — total revenue is the sum of the slice revenues
-- statement:
--   Let the type law satisfy Assumption 2, let $d\ge2$, $c>0$, $\delta\in(0,1)$, and let $x$ be a real price function whose revenue series $\sum_t\delta^t\,\mathrm{Revenue}(\pi,t)$ is summable. Then
--   $$
--   \mathrm{Revenue}(\pi)=\sum_{j\ge 1}\mathrm{Revenue}_{[s_j,s_{j+1})}(\pi),
--   $$
--   the sum running over the introductions of the schedule, and the series on the right is summable.
--
--   Customers arriving before $s_1$ pay nothing. Together with Observation 1 this reduces maximizing $\mathrm{Revenue}(\pi)$ for fixed introduction times to maximizing each slice separately.
--
--   Differences from the source:
--   - encoding: (1−F)/f monotonically decreasing on the support, differentiable density f → f > 0, (1−F)/f antitone and f differentiable on (0, ζ); reason: Lean has x/0 = 0, which on the closed interval would exclude Beta(2,2) with f(0) = 0; f > 0 on (0, ζ) follows from the source; the uniform example of p.24 is differentiable only on the interior
--   - encoding: (possibly infinite) sequence of introductions and prices x_{j,m} for m ≤ min(j−1, n), with x₀ = 0 → a schedule with J : ℕ∞ and a total function x : ℕ → ℕ → ℝ read through classPrice; reason: the same policies; unused entries of x enter nothing and class 0 always costs 0
--   - encoding: (10) sums over s_j ≤ t ≤ s_{j+1}+d−2 → a sum over all t with the printed age range, and s_{j+1} = ∞ at the last introduction of a finite schedule; reason: the age range is empty outside the printed times; a finite schedule has a last slice that the printed formula needs ∞ for
--   - encoding: the decomposition, stated without comment on convergence → assumes the revenue series is summable; reason: Lean’s sum of a non-summable series is 0; a myopic customer pays at most θ·t, so the positive part converges and a non-summable series diverges to −∞
-- source:
--   Kash, Key & Zoumpoulis, Optimal Pricing and Introduction Timing of Technology Upgrades in Subscription-Based Services, SSRN 3934603 (Aug. 3, 2022), §4.2, p.14

import Mathlib
import Definitions.Def_KashUpgrade_Assumption2
import Definitions.Def_KashUpgrade_totalRevenue
import Definitions.Def_KashUpgrade_sliceRevenue
open Classical

namespace KashUpgrade

/-- **Revenue decomposes into slices.** Kash, Key & Zoumpoulis, *Optimal Pricing and Introduction Timing of Technology Upgrades in Subscription-Based Services*, SSRN 3934603 (Aug. 3, 2022), §4.2, p.14: the total revenue is the sum of the slice
revenues over the introductions `j ≥ 1`, which reduces maximizing `Revenue(π)` to maximizing each
`Revenue_[s_j, s_{j+1})` separately.

**Formalization Note** The sum over `j` is a `HasSum` over `ℕ`, with the term `0` for `j = 0` and for
`j` beyond a finite schedule. The hypothesis is that the revenue series itself is summable, for
arbitrary real prices. -/
theorem slice_decomposition {f : ℝ → ℝ} {ζ : ENNReal} (hf : Assumption2 f ζ) (S : Schedule) {d : ℕ} {c δ : ℝ} (hd : 2 ≤ d) (hc : 0 < c) (hδ₀ : 0 < δ) (hδ₁ : δ < 1) (x : ℕ → ℕ → ℝ) (hx : Summable (discountedRevenue f S d c δ x)) : HasSum (fun j => if 1 ≤ j ∧ IsIntroduced S j then sliceRevenue f S d c δ j x else 0) (totalRevenue f S d c δ x) := by sorry

end KashUpgrade
