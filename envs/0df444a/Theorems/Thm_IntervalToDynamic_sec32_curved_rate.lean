-- Prove2me | Theorems.Thm_IntervalToDynamic_sec32_curved_rate
-- name    : IntervalToDynamic.sec32_curved_rate
-- status  : Open
-- author  : @iris
-- created : 2026-11-05T20:21:30.995286+00:00
-- url     : https://prove2.me/theorems/850a69e9-68a6-43b0-8510-bbf86007b73b
-- title:
--   §3.2, p.11 — the curved rate in explicit form
-- statement:
--   Let $D_{\mathcal X}>0$, $\mathcal Y=\mathcal B(D_{\mathcal X})$, and for $t\in[T]$ let $h_t$ be differentiable and $H$-smooth on $\mathcal Y$ with $H>0$, $u_t\in\mathcal B(D_{\mathcal X}/2)$, $c_t=u_t-H^{-1}\nabla h_t(u_t)\in\mathcal Y$ and $y_t\in\mathcal Y$. If $\rho>0$ bounds regret uniformly on all intervals, $\text{I-Reg}_I(z)\le\rho$ for every $I\subseteq[T]$ and $z\in\mathcal Y$, then
--   $$
--   \sum_{t=1}^T\bigl(h_t(y_t)-h_t(u_t)\bigr)\le\Bigl(2+\frac H8\Bigr)\Bigl(\rho+\rho^{2/3}P_T^{2/3}(2T)^{1/3}\Bigr).
--   $$
--
--   This is the display of §3.2 with $B=\sqrt\rho$, $\varepsilon=1/2$: each interval's total error is at most $H\rho/8$, and $K\le1+\rho^{-1/3}P_T^{2/3}(2T)^{1/3}$.
--
--   Differences from the source:
--   - reading: D-Reg_T ≤ (2 + H_h/8) K ρ_T = O(ρ_T + ρ_T^{2/3} P_T^{2/3} T^{1/3}) → the explicit bound (2 + H/8)(ρ + ρ^{2/3} P_T^{2/3} (2T)^{1/3}); reason: the printed O-form, with its constant written out, so this implies the display
--   - generalization: ρ_T ≥ 1 → `0 < ρ`; reason: the argument needs only ρ > 0, and ρ_T ≥ 1 is a case of it
--   - generalization: h_t the curved surrogates of the run, and comparators u_t ∈ X → any H-smooth h_t on Y with c_t ∈ Y, any y_t ∈ Y, and any u_t ∈ B(D_X/2); reason: the statement is pathwise, and Lemma 14 makes the run an instance (X ⊆ B(D_X/2) by Assumption 1)
--   - encoding: h_t differentiable with gradient ∇h_t on Y → a gradient oracle `gh t` with `HasGradientWithinAt` on Y; reason: Y has nonempty interior, so the oracle is the gradient
-- source:
--   Wang–Zhao–Zhou, On the Relation Between Interval Regret and Dynamic Regret, arXiv:2609.34423, §3.2, p.11

import Mathlib
import Definitions.Def_IntervalToDynamic_intervalRegret
import Definitions.Def_IntervalToDynamic_IsSmoothOn
import Definitions.Def_ModernOnlineLearning_Dynamic_Defs
open ModernOnlineLearning.Dynamic (dynamicRegret pathLength)

namespace IntervalToDynamic

/-- The curved rate of §3.2. Wang–Zhao–Zhou, *On the Relation Between Interval Regret and Dynamic Regret*, arXiv:2609.34423, §3.2, p.11.

Let `h_t` be differentiable and `H`-smooth on `Y = B(D_X)`, `H > 0`, with
`c_t = u_t − H⁻¹ ∇h_t(u_t) ∈ Y`, `u_t ∈ B(D_X/2)`, `y_t ∈ Y`. If `ρ > 0` bounds regret uniformly on all
intervals, `I-Reg_I(z) ≤ ρ` for every `I ⊆ [T]` and `z ∈ Y`, then
`∑_{t ≤ T} (h_t(y_t) − h_t(u_t)) ≤ (2 + H/8) (ρ + ρ^{2/3} P_T^{2/3} (2T)^{1/3})`.

**Formalization Note.** This is the explicit form of the display `D-Reg_T ≤ (2 + H_h/8) K ρ_T =
O(ρ_T + ρ_T^{2/3} P_T^{2/3} T^{1/3})`, with `B = √ρ`, `ε = 1/2`. The statement is pathwise. Powers
are `Real.rpow` with real exponents, and `0 ^ (2/3) = 0`. -/
theorem sec32_curved_rate {d : ℕ} (hd : 0 < d) (T : ℕ) (hT : 1 ≤ T) (DX H ρ : ℝ) (hDX : 0 < DX)
    (hH : 0 < H) (hρ : 0 < ρ) (h : ℕ → EuclideanSpace ℝ (Fin d) → ℝ) (gh : ℕ → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) (y u : ℕ → EuclideanSpace ℝ (Fin d))
    (hy : ∀ t ∈ Finset.Icc 1 T, y t ∈ Metric.closedBall 0 DX)
    (hu : ∀ t ∈ Finset.Icc 1 T, u t ∈ Metric.closedBall 0 (DX / 2))
    (hsm : ∀ t ∈ Finset.Icc 1 T, IsSmoothOn (Metric.closedBall 0 DX) H (h t) (gh t))
    (hc : ∀ t ∈ Finset.Icc 1 T, u t - H⁻¹ • gh t (u t) ∈ Metric.closedBall 0 DX)
    (hreg : ∀ a b : ℕ, 1 ≤ a → a ≤ b → b ≤ T → ∀ z ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) DX,
      intervalRegret h y a b z ≤ ρ) :
    dynamicRegret h y u T ≤
      (2 + H / 8) * (ρ + ρ ^ (2 / 3 : ℝ) * pathLength u T ^ (2 / 3 : ℝ) *
        (2 * (T : ℝ)) ^ (1 / 3 : ℝ)) := by sorry

end IntervalToDynamic
