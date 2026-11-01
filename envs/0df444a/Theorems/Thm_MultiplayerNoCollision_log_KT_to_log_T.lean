-- Prove2me | Theorems.Thm_MultiplayerNoCollision_log_KT_to_log_T
-- name    : MultiplayerNoCollision.log_KT_to_log_T
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T09:24:36.62699+00:00
-- url     : https://prove2.me/theorems/bb2c29b4-1bbd-40c9-871f-2b34c5a335f0
-- title:
--   Proof of Theorem 1, p.13 — $\min\{mT,O(mK\log(KT)/\Delta^2)\}=O(mK\log(T)/\Delta^2)$ (corrected: $\max\{1,\log T\}$ for $T=1$)
-- statement:
--   There is an absolute constant $C_0$ such that for all integers $m\ge2$, $K\ge m+1$, $T\ge1$ and every real $0<\Delta\le1$, with $g=128K\log(3Km^2T^2)$ and $X=625g/\Delta^2+4m\log(m^2T)/\Delta$,
--   $$\Delta^2\cdot m\cdot\min\{T,\lceil X\rceil\}\le C_0\,mK\max\{1,\log T\}.$$
--
--   This removes the $K$ inside the logarithm of the proof's bound: either $K\le T$ and $\log(KT)\le2\log T$, or $K>T$ and $\min\{mT,\cdot\}\le mK$.
--
--   Differences from the source:
--   - correction: O(mK log(T)/∆²) → C₀ mK max{1, log T}/∆²; reason: at T = 1 the printed right side is 0 while the left side min{m, O(·)} is positive (m = 2, K = 3, ∆ = 1: ∆²·m·min{1, ⌈X⌉} = 2 > 0); for T ≥ 2, max{1, log T} ≤ log T/log 2
--   - reading: min{mT, O(mK log(KT)/∆²)} → m · min{T, ⌈625g/∆² + 4m log(m²T)/∆⌉} with an explicit absolute constant C₀ chosen before m, K, T, ∆; reason: the O-term is the explicit quantity of the proof (p.13); O(·) means an absolute constant (p.4)
--   - encoding: bound with ∆² in the denominator → both sides multiplied by ∆²; reason: ∆ > 0 here; avoids Lean's x/0 = 0
--   - encoding: ∆ = µ_m − µ_{m+1} for means in [0,1] → any real ∆ with 0 < ∆ ≤ 1; reason: every such ∆ arises from means in [0,1] and vice versa
--   - encoding: K ≥ m (Assumption 1) → K ≥ m + 1; reason: ∆ = µ_m − µ_{m+1} and the stopping rule of Algorithm 1 need an (m+1)-th arm; only the undefined case K = m is excluded
-- source:
--   Lugosi, Mehrabian, Multiplayer bandits without observing collision information, arXiv:1808.08416v2, proof of Theorem 1, p.13

import Mathlib
import Definitions.Def_MultiplayerNoCollision_algorithm1

namespace MultiplayerNoCollision

/-- **Proof of Theorem 1: from `log(KT)` to `log T`.**
Lugosi, Mehrabian, *Multiplayer bandits without observing collision information*,
arXiv:1808.08416v2, proof of Theorem 1, p.13: "The `O(log(KT))` can be replaced with `O(log(T))`,
noting that `min{mT, O(mK log(KT)/∆²)} = O(mK log(T)/∆²)`."

There is an absolute constant `C₀` such that for all `m ≥ 2`, `K ≥ m + 1`, `T ≥ 1` and
`0 < ∆ ≤ 1`, with `g = 128 K log(3 K m² T²)` and `X = 625g/∆² + 4m log(m²T)/∆`,
`∆² · m · min{T, ⌈X⌉} ≤ C₀ · m K · max{1, log T}`.

**Formalization Note.** The page's `O(mK log(KT)/∆²)` is the explicit quantity of the proof
`m · min{T, ⌈X⌉}`, which is `min{mT, m⌈X⌉}`. The bound is multiplied by `∆²`.
`max{1, log T}` replaces `log T`: at `T = 1` the printed right side is `0` while the left side is
positive (correction; for `T ≥ 2`, `max{1, log T} ≤ log T / log 2`). `∆ ≤ 1` holds for means in
`[0, 1]`. `C₀` is chosen before `m, K, T, ∆`. -/
theorem log_KT_to_log_T : ∃ C₀ : ℝ, ∀ m K T : ℕ, 2 ≤ m → m + 1 ≤ K → 1 ≤ T →
    ∀ Δ : ℝ, 0 < Δ → Δ ≤ 1 →
      Δ ^ 2 * ((m : ℝ) * ((min T ⌈625 * gParam m K T / Δ ^ 2 +
          4 * m * Real.log ((m : ℝ) ^ 2 * T) / Δ⌉₊ : ℕ) : ℝ)) ≤
        C₀ * m * K * max 1 (Real.log T) := by sorry

end MultiplayerNoCollision
