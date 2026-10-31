-- Prove2me | Theorems.Thm_KashUpgrade_observation_1
-- name    : KashUpgrade.observation_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T03:24:14.994767+00:00
-- url     : https://prove2.me/theorems/18ecab48-3980-4742-830c-3b5c60a61f9a
-- title:
--   Observation 1, p.14 — the slice revenue depends only on the listed prices
-- statement:
--   Fix a schedule, $d\ge 2$, an introduction $j\ge 1$, and $n$ bounding the upgrade experience of slice $j$. If two price functions agree on the prices
--   $$
--   x_{1,0},\ x_{2,0},\ \dots,\ x_{j,0},\ x_{j+1,1},\ x_{j+2,2},\ \dots,\ x_{j+n,n},
--   $$
--   then they have the same revenue $\mathrm{Revenue}_{[s_j,s_{j+1})}$.
--
--   This is what lets the optimal pricing problem decouple across slices: each upgrade price $x_{k,m}$ with $m\ge1$ occurs in one slice only, namely $j=k-m$.
--
--   Differences from the source:
--   - encoding: (possibly infinite) sequence of introductions and prices x_{j,m} for m ≤ min(j−1, n), with x₀ = 0 → a schedule with J : ℕ∞ and a total function x : ℕ → ℕ → ℝ read through classPrice; reason: the same policies; unused entries of x enter nothing and class 0 always costs 0
--   - encoding: (10) sums over s_j ≤ t ≤ s_{j+1}+d−2 → a sum over all t with the printed age range, and s_{j+1} = ∞ at the last introduction of a finite schedule; reason: the age range is empty outside the printed times; a finite schedule has a last slice that the printed formula needs ∞ for
--   - generalization: n the maximum possible customer upgrade experience → any n bounding the upgrade experience of the slice; reason: the source’s n is such a bound, and the larger indices have zero weight or unused prices
--   - encoding: Revenue is a function of the listed prices, and no other prices → two price functions agreeing on the listed prices have equal slice revenue; reason: the same statement, for functions on a total price type
--   - generalization: the standing assumptions of §3–§4 (Assumption 2 on f, c > 0, δ ∈ (0, 1)) → arbitrary f, c and δ; reason: the integrands agree pointwise, so the statement holds without them and specializes to the source's
-- source:
--   Kash, Key & Zoumpoulis, Optimal Pricing and Introduction Timing of Technology Upgrades in Subscription-Based Services, SSRN 3934603 (Aug. 3, 2022), Observation 1, p.14

import Mathlib
import Definitions.Def_KashUpgrade_IsUpgradeBoundAt
import Definitions.Def_KashUpgrade_sliceRevenue

namespace KashUpgrade

/-- **Observation 1.** Kash, Key & Zoumpoulis, *Optimal Pricing and Introduction Timing of Technology Upgrades in Subscription-Based Services*, SSRN 3934603 (Aug. 3, 2022), Observation 1, p.14: `Revenue_[s_j, s_{j+1})` is a function of the
prices `x_{1,0}, …, x_{j,0}, x_{j+1,1}, …, x_{j+n,n}`, and no other prices. Two price functions
that agree on these prices have the same slice revenue.

**Formalization Note** The hypothesis is that `n` bounds the upgrade experience of this slice, which
holds for the paper's `n`. -/
theorem observation_1 (f : ℝ → ℝ) (S : Schedule) {d : ℕ} (c δ : ℝ) (hd : 2 ≤ d) {j n : ℕ} (hj : 1 ≤ j) (hjS : IsIntroduced S j) (hn : IsUpgradeBoundAt S d j n) (x x' : ℕ → ℕ → ℝ) (h₀ : ∀ i, 1 ≤ i → i ≤ j → x i 0 = x' i 0) (h₁ : ∀ i, 1 ≤ i → i ≤ n → x (j + i) i = x' (j + i) i) : sliceRevenue f S d c δ j x = sliceRevenue f S d c δ j x' := by sorry

end KashUpgrade
