-- Prove2me | Theorems.Thm_OnlineCAP_theorem_4_3
-- name    : OnlineCAP.theorem_4_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T07:26:29.43946+00:00
-- url     : https://prove2.me/theorems/6f97ca3d-a5a1-4be9-a673-82f9dcf975ed
-- title:
--   Theorem 4.3 — online rounding for bottomless rectangles with loss O(log log n)
-- statement:
--   There is a function $\alpha(n)=O(\log\log n)$ such that for every finite point set $P\subseteq\mathbb R^2$ with $n=|P|$ there is a randomized online algorithm with the following property. Given online a sequence of bottomless rectangles $R_1,R_2,\dots$ and an online fractional hitting set $x^1\le x^2\le\cdots$ (with $x^t(R_{t'}\cap P)\ge1$ for $t'\le t$), it maintains an increasing hitting set $H_t\subseteq P$ of $R_1,\dots,R_t$, for every outcome of its coins, such that
--   $$\Pr[p\in H_t]\le\alpha(n)\,x^t_p\qquad\text{for every } p\in P\text{ and every time } t .$$
--   The requests and $x$ are independent of the algorithm's randomness. In the terminology of Definition 4.11, the traces of bottomless rectangles on $P$ have an $O(\log\log n)$-rounding algorithm.
--
--   Differences from the source:
--   - encoding: Pr[p ∈ H] ≤ O(log log n) x_p → α : ℕ → ℝ with α =O[atTop] log log n and Pr[p ∈ H_t] ≤ α(n) x^t_p; reason: one function of n for all point sets; natural logarithms
--   - reading: Pr[p ∈ H] ≤ … x_p → at every time step t, with the current x^t_p; reason: §4.1 introduces x^t_p as "the extent to which point p is bought in response to the first t requests" and the proof (p.20) bounds Pr[p ∈ H_t] for every t
--   - reading: maintains an online hitting set H → H_t hits every request so far for every outcome of the coins; reason: Algorithm 2 always outputs a hitting set ("satisfying all requests up until the current time step", p.18)
--   - generalization: n ≥ 1 (standing assumption, p.15) → any finite P; reason: for P = ∅ there are no valid inputs
--   - encoding: an online sequence of rectangles with fractional solution x → finite valid input lists of (R_t ∩ P, x^t), the universe being P; reason: the guarantee at time t concerns the prefix; a rectangle enters through its trace on P
-- source:
--   Hathcock, Subramanian, Umboh, Zlatin, Weighted and Unweighted Online Connectivity Augmentation via Geometric Hitting Set (manuscript of Nov. 3, 2026, sha256 e3b9cb64…), Theorem 4.3, p.15 (proof p.20)

import Mathlib
import Definitions.Def_OnlineCAP_RandOnlineAlg
import Definitions.Def_OnlineCAP_IsRounding
import Definitions.Def_OnlineCAP_traceFam
import Definitions.Def_OnlineCAP_IsBottomless

open MeasureTheory Filter Asymptotics

namespace OnlineCAP

/-- **Theorem 4.3 (online rounding for bottomless rectangles).** Hathcock–Subramanian–Umboh–Zlatin, *Weighted and Unweighted Online Connectivity
Augmentation via Geometric Hitting Set*, manuscript of Nov. 3, 2026 (sha256 e3b9cb64…), Theorem 4.3, p.15 (PDF
p.15): "There exists a randomized algorithm that given an online sequence of bottomless rectangles
and an online fractional solution x, maintains an online hitting set H such that
Pr[p ∈ H] ≤ O(log log n)xp for every p ∈ P. The request sequence and x are independent of the
algorithm's randomness."

There is a function `α(n) = O(log log n)` such that for every finite point set `P ⊆ ℝ²` with
`n = |P|` there is an `α(n)`-rounding algorithm for the traces on `P` of bottomless rectangles:
on every online sequence of bottomless rectangles `R_t` with a monotone fractional hitting set
`x^t`, it maintains for every outcome of its coins an increasing hitting set `H_t ⊆ P` with
`Pr[p ∈ H_t] ≤ α(n) x^t_p` for every point `p` and time `t`.

**Formalization Note.** "Pr[p ∈ H] ≤ O(log log n) x_p" holds at every time step with the current
vector `x^t` (§4.1, p.15; proof, p.20). `O(·)` is `Asymptotics.IsBigO` along `n → ∞`, natural
logarithms. The standing assumption `n ≥ 1` (p.15) is dropped: for `P = ∅` the claim is
trivial. -/
theorem theorem_4_3 : ∃ α : ℕ → ℝ, α =O[atTop] (fun n : ℕ => Real.log (Real.log n)) ∧
    ∀ P : Finset (ℝ × ℝ), ∃ A : RandOnlineAlg ↥P (Set ↥P × (↥P → ℝ)),
      IsRounding (traceFam P IsBottomless) A (α P.card) := by sorry

end OnlineCAP
