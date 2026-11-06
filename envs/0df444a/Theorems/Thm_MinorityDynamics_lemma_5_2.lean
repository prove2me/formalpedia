-- Prove2me | Theorems.Thm_MinorityDynamics_lemma_5_2
-- name    : MinorityDynamics.lemma_5_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-05T20:15:47.042584+00:00
-- url     : https://prove2.me/theorems/9446b926-a6e7-453d-ac0a-184412255a1d
-- title:
--   Lemma 5.2 — an integral bound for a lattice sum
-- statement:
--   Let $n\ge1$ be an integer, let $J\subseteq\mathbb R$ be a bounded interval, and let $v,r$ be nonnegative bounded functions on $J$ such that $v$ is non-increasing on $J$ and $r$ is unimodal on $J$ (non-decreasing up to some point $m$ and non-increasing after it). Then
--   $$\sum_{x\in J\cap n^{-1}\mathbb Z} v(x)\,r(x)\;\le\; n\int_J v(x)r(x)\,dx+\Big(\sup_J v\Big)\Big(\sup_J r\Big).$$
--
--   The lemma converts the lattice sums over states $x=s/n$ in the transition estimates (§5) into integrals, at the cost of one peak value.
--
--   Differences from the source:
--   - encoding: a bounded real interval J → a bounded order-connected set J ⊆ ℝ (any interval kind, possibly empty or a point); reason: order-connected subsets of ℝ are exactly the intervals; same instances
--   - encoding: r is unimodal → ∃ m, r is monotone on J ∩ (−∞, m] and antitone on J ∩ [m, ∞); reason: the meaning used in the proof (r₁ ≤ ⋯ ≤ r_j ≥ ⋯ ≥ r_l); same instances
--   - encoding: ∑ over x ∈ J ∩ n^{−1}ℤ, sup_J v → a finite sum over integers z with z/n ∈ J; sSup of v(J); reason: J is bounded so the sum is finite; sSup of a bounded nonempty set is the supremum (both sides are 0 when J is empty)
-- source:
--   Giakkoupis, Los, Sauerwald, Ziccardi, Minority Dynamics with Small Samples, manuscript (STOC 2027 submission), Lemma 5.2, p.23

import Mathlib

set_option autoImplicit false

open Classical

namespace MinorityDynamics

/-- **Lemma 5.2 (An integral bound for a lattice sum)** (Giakkoupis, Los, Sauerwald, Ziccardi, *Minority Dynamics with Small Samples*, manuscript (STOC 2027 submission), p.23 = PDF p.25): "Let J be a
bounded real interval, and let v, r be nonnegative bounded functions on J. Suppose v is
non-increasing and r is unimodal. Then ∑_{x∈J∩n^{−1}Z} v(x)r(x) ≤ n ∫_J v(x)r(x) dx + (sup_J v)(sup_J r)."

**Formalization Note** A real interval is an order-connected subset of `ℝ` (any of the interval
kinds, possibly empty or a point). "r is unimodal" is "non-decreasing then non-increasing" (the
proof, p.23: `r₁ ≤ ⋯ ≤ rⱼ ≥ ⋯ ≥ r_l`): there is `m` with `r` monotone on `J ∩ (−∞, m]` and antitone
on `J ∩ [m, ∞)`. The lattice sum is a finite sum (`J` is bounded) over the integers `z` with
`z/n ∈ J`. `sup_J v` is `sSup (v '' J)`, which is `0` for empty `J` (then both sides are `0`).
The lemma holds for every positive integer `n`; the integral is the Lebesgue integral over `J`,
of a bounded function that is measurable on `J` (monotone pieces), so no integrability hypothesis
is added. -/
theorem lemma_5_2 (n : ℕ) (hn : 0 < n) (J : Set ℝ) (hJ : J.OrdConnected)
    (hJb : Bornology.IsBounded J) (v r : ℝ → ℝ) (hv0 : ∀ x ∈ J, 0 ≤ v x)
    (hr0 : ∀ x ∈ J, 0 ≤ r x) (hvb : BddAbove (v '' J)) (hrb : BddAbove (r '' J))
    (hv : AntitoneOn v J)
    (hr : ∃ m : ℝ, MonotoneOn r (J ∩ Set.Iic m) ∧ AntitoneOn r (J ∩ Set.Ici m)) :
    ∑ᶠ (z : ℤ) (_ : (z : ℝ) / n ∈ J), v ((z : ℝ) / n) * r ((z : ℝ) / n) ≤
      (n : ℝ) * ∫ x in J, v x * r x + sSup (v '' J) * sSup (r '' J) := by sorry

end MinorityDynamics
