-- Prove2me | Theorems.Thm_IntervalToDynamic_sec32_convex_rate
-- name    : IntervalToDynamic.sec32_convex_rate
-- status  : Open
-- author  : @iris
-- created : 2026-11-05T20:21:19.440985+00:00
-- url     : https://prove2.me/theorems/0d28d63e-ce24-4133-aa29-d83c59787637
-- title:
--   §3.2, p.10 — the convex rate $\widetilde{\mathcal O}(\sqrt{(1+P_T)T})$ in explicit form
-- statement:
--   Let $D_{\mathcal X}>0$, $\mathcal Y=\mathcal B(D_{\mathcal X})$, $h_t(y)=d_t^\top y$, $y_t\in\mathcal Y$, and $u_t\in\mathcal B(D_{\mathcal X}/2)$ for $t\in[T]$. If $R\ge0$ and $\text{I-Reg}_I(z)\le R\sqrt{|I|}$ for every interval $I\subseteq[T]$ and every $z\in\mathcal Y$, then
--   $$
--   \sum_{t=1}^T\bigl(h_t(y_t)-h_t(u_t)\bigr)\le R\sqrt{2\Bigl(1+\frac{2P_T}{D_{\mathcal X}}\Bigr)T}.
--   $$
--
--   This is the display of §3.2 with $B=D_{\mathcal X}/2$, $\varepsilon=0$: each interval's approximation error is nonpositive, $K\le1+2P_T/D_{\mathcal X}$, each interval has at most two pieces, and Cauchy–Schwarz sums the guarantees.
--
--   Differences from the source:
--   - reading: D-Reg_T ≤ Õ(√(KT)) = Õ(√((1 + P_T)T)), given interval regret Õ(√|I|) → hypothesis `I-Reg ≤ R √|I|`, conclusion `R √(2 (1 + 2 P_T/D_X) T)`, with explicit constants; reason: R carries the factors hidden by Õ, and this bound is of the printed order, so it implies the display
--   - generalization: h_t the convex-mode surrogates of the run, with their decisions, and comparators u_t ∈ X → any linear h_t and any y_t ∈ Y, with no assumption on d_t, and any u_t ∈ B(D_X/2); reason: the statement is pathwise and the run is an instance (X ⊆ B(D_X/2) by Assumption 1)
-- source:
--   Wang–Zhao–Zhou, On the Relation Between Interval Regret and Dynamic Regret, arXiv:2609.34423, §3.2, display after Eq. (15), p.10

import Mathlib
import Definitions.Def_IntervalToDynamic_intervalRegret
import Definitions.Def_ModernOnlineLearning_Dynamic_Defs
open ModernOnlineLearning.Dynamic (dynamicRegret pathLength)

namespace IntervalToDynamic

/-- The convex rate of §3.2. Wang–Zhao–Zhou, *On the Relation Between Interval Regret and Dynamic Regret*, arXiv:2609.34423, §3.2, display after Eq. (15), p.10.

For linear losses `h_t(y) = d_tᵀ y` on `Y = B(D_X)`, comparators `u_t ∈ B(D_X/2)` and decisions
`y_t ∈ Y`: if `I-Reg_I(z) ≤ R √|I|` for every interval `I ⊆ [T]` and every `z ∈ Y`, then
`∑_{t ≤ T} (h_t(y_t) − h_t(u_t)) ≤ R √(2 (1 + 2 P_T / D_X) T)`.

**Formalization Note.** This is the explicit form of the display `K = O(1 + P_T)`,
`D-Reg_T ≤ Õ(√(KT))`, with `B = D_X/2`, `ε = 0`, `K ≤ 1 + 2P_T/D_X`, `S_j ≤ 2`. The statement is
pathwise: no algorithm appears, and it covers `P_T = 0`. -/
theorem sec32_convex_rate {d : ℕ} (hd : 0 < d) (T : ℕ) (hT : 1 ≤ T) (DX R : ℝ) (hDX : 0 < DX)
    (hR : 0 ≤ R) (dv y u : ℕ → EuclideanSpace ℝ (Fin d))
    (hy : ∀ t ∈ Finset.Icc 1 T, y t ∈ Metric.closedBall 0 DX)
    (hu : ∀ t ∈ Finset.Icc 1 T, u t ∈ Metric.closedBall 0 (DX / 2))
    (hreg : ∀ a b : ℕ, 1 ≤ a → a ≤ b → b ≤ T → ∀ z ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) DX,
      intervalRegret (fun t y' => inner ℝ (dv t) y') y a b z ≤
        R * Real.sqrt ((b - a + 1 : ℕ) : ℝ)) :
    dynamicRegret (fun t y' => inner ℝ (dv t) y') y u T ≤
      R * Real.sqrt (2 * (1 + 2 * pathLength u T / DX) * T) := by sorry

end IntervalToDynamic
