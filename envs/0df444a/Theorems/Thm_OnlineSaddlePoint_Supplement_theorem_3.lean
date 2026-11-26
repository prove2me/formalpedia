-- Prove2me | Theorems.Thm_OnlineSaddlePoint_Supplement_theorem_3
-- name    : OnlineSaddlePoint.Supplement.theorem_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-26T21:56:26.173024+00:00
-- url     : https://prove2.me/theorems/a6fad193-e677-4783-b158-ac3169096d99
-- title:
--   Theorem 3 — OMG-RFTL has SP-Regret $\le 32G\sqrt T(1+\ln T)+2\sqrt T\max\{\ln d_1,\ln d_2\}+2\max\{d_1,d_2\}GTe^{-\sqrt T}$
-- statement:
--   Let $d_1,d_2\in\mathbb N$, $T\ge1$, and let $A_1,\dots,A_T$ be $d_1\times d_2$ matrices with entries in $[-1,1]$. Let $\bar{\mathcal L}_t(x,y)=x^\top A_t y$ and let $G>0$, $G\le1$, be a common Lipschitz constant of $\bar{\mathcal L}_1,\dots,\bar{\mathcal L}_T$ on $\Delta_X\times\Delta_Y$ with respect to $\|\cdot\|_1$. Set
--
--   $$
--   \eta=\frac{\sqrt T}{G},\qquad \theta=e^{-\eta G}=e^{-\sqrt T},
--   $$
--
--   and assume $\theta\le\min\{1/d_1,1/d_2\}$. Let $(x_t,y_t)_{t=1}^{T+1}$ be a run of OMG-RFTL (Algorithm 3): Saddle-Point Follow-the-Leader on the restricted simplexes $\Delta_{X,\theta}\times\Delta_{Y,\theta}$ for the regularized payoffs $x^\top A_ty+\frac1\eta R_X(x)-\frac1\eta R_Y(y)$, with the entropic regularizers $R_X(x)=\sum_i x_i\ln x_i+\ln d_1$, $R_Y(y)=\sum_j y_j\ln y_j+\ln d_2$. Then
--
--   $$
--   \left|\sum_{t=1}^T x_t^\top A_t y_t-\min_{x\in\Delta_X}\max_{y\in\Delta_Y}\sum_{t=1}^T x^\top A_t y\right|
--   \le 32G\sqrt T(1+\ln T)+2\sqrt T\max\{\ln d_1,\ln d_2\}+2\max\{d_1,d_2\}\,G\,T e^{-\sqrt T}.
--   $$
--
--   The bound is $O(\ln(T)\sqrt T+\sqrt T\max\{\ln d_1,\ln d_2\})+o(1)\max\{d_1,d_2\}$: for matrix games the SP-Regret grows only logarithmically in the number of actions, against the linear dependence of the general convex-concave bound (Corollary 1).
--
--   Differences from the source:
--   - generalization: $G_{\bar{\mathcal L}}$ \"the Lipschitz constant (with respect to $\|\cdot\|_1$)\" of $x^\top A_ty$ → any common $\ell_1$ Lipschitz constant $G$ of the $\bar{\mathcal L}_t$ on $\Delta_X\times\Delta_Y$ with $0<G\le1$; reason: the least such constant is at most $1$ because the entries lie in $[-1,1]$ (used in the proof, pp.18–19) and must be positive for $\eta=\sqrt T/G$ to be defined, so the paper's constant is one of the admitted values
--   - generalization: Algorithm 3's input condition $\theta<\min\{1/d_1,1/d_2\}$ → $\theta\le\min\{1/d_1,1/d_2\}$, as in the theorem's own statement; reason: the theorem states $\le$; the restricted simplexes are nonempty also at equality, and the strict case is included
--   - reading: OMG-RFTL updates $\arg\min_{x\in\Delta_{X,\theta}}\max_{y\in\Delta_{Y,\theta}}\sum_{\tau=1}^t\mathcal L_t(x,y)$ → an SP-FTL run (`IsSPFTLRun`) on $\Delta_{X,\theta}\times\Delta_{Y,\theta}$ for the regularized payoffs, summing $\mathcal L_\tau$; reason: the summand index is a typo, as in Algorithm 2; OMG-RFTL is \"an instantiation of SP-RFTL\" (p.16)
--   - encoding: $\eta>0$ in Algorithm 3 → $T\ge1$; reason: with $\eta=\sqrt T/G$, $\eta>0$ holds exactly when $T\ge1$
--   - reading: the final line \"$=O(\ln(T)\sqrt T+\sqrt T\max\{\ln d_1,\ln d_2\})+o(1)\max\{d_1,d_2\}$\" → not restated; reason: it is the asymptotic reading of the explicit inequality, which is stated in full
--   - encoding: $\mathbb R^{d}$ with $\|\cdot\|_1$ → `PiLp 1 (fun _ : Fin d => ℝ)`, whose norm is $\sum_i|z_i|$; reason: the same normed space
--   - encoding: $\ln$ → `Real.log`; reason: the natural logarithm; only evaluated at positive arguments in the bound
--   - encoding: $x^\top A_t y$ → $\sum_i\sum_j x_i(A_t)_{ij}y_j$ (`bilinearPayoff`); reason: the same number
--   - encoding: $\min_{x\in\Delta_X}\max_{y\in\Delta_Y}$ → `sInf`/`sSup` of images (`minimaxValue`); reason: attained on the compact simplexes for the continuous bilinear payoff
-- source:
--   Rivera Cardoso, Wang, Xu, The Online Saddle Point Problem and Online Convex Optimization with Knapsacks, arXiv:1806.08301v3, Theorem 3, pp.16–17 (proof pp.17–19); Algorithm 3, p.16

import Mathlib
import Definitions.Def_OnlineSaddlePoint_spRegret
import Definitions.Def_OnlineSaddlePoint_IsLipschitzPayoff
import Definitions.Def_OnlineSaddlePoint_IsSPFTLRun
import Definitions.Def_OnlineSaddlePoint_Supplement_regularizedPayoff
import Definitions.Def_OnlineSaddlePoint_Supplement_restrictedSimplex
import Definitions.Def_OnlineSaddlePoint_Supplement_entropicRegularizer
import Definitions.Def_OnlineSaddlePoint_Supplement_bilinearPayoff

namespace OnlineSaddlePoint.Supplement

open OnlineSaddlePoint

/-- **Theorem 3 (OMG-RFTL has `O(ln(T)√T + √T max{ln d₁, ln d₂})` SP-Regret).** Rivera Cardoso, Wang,
Xu, arXiv:1806.08301v3, Theorem 3, pp.16–17: "Let `{A_t}_{t=1}^T` be an arbitrary sequence of matrices
in `[−1, 1]^{d₁×d₂}`. Let `G_𝓛̄` be the Lipschitz constant (with respect to `‖·‖₁`) of `𝓛̄_t ≜ xᵀA_t y`
for `t = 1, ..., T`. Let `{(x_t, y_t)}_{t=1}^T` be the iterates of OMG-RFTL and choose
`θ = e^{−ηG_𝓛̄} ≤ min{1/d₁, 1/d₂}` such that `|ln(θ)|/η = G_𝓛̄`. By setting `η = √T/G_𝓛̄` in
Algorithm 3, it holds that `|∑_{t=1}^T x_tᵀA_t y_t − min_{x∈Δ_X} max_{y∈Δ_Y} ∑_{t=1}^T xᵀA_t y|
≤ 32 G_𝓛̄ √T (1 + ln(T)) + 2√T max{ln d₁, ln d₂} + 2 max{d₁, d₂} G_𝓛̄ T e^{−√T}`."

OMG-RFTL (Algorithm 3, p.16) is SP-FTL run on `Δ_{X,θ} × Δ_{Y,θ}` on the regularized payoffs
`xᵀA_t y + (1/η)R_X(x) − (1/η)R_Y(y)` with the entropic regularizers `R_X`, `R_Y`.

**Formalization Note.** Strategies are in `PiLp 1 (fun _ : Fin d => ℝ)` (`ℓ₁` norm);
`Δ_X = restrictedSimplex d₁ 0`, `Δ_{X,θ} = restrictedSimplex d₁ θ`. `G_𝓛̄` is any common `ℓ₁`
Lipschitz constant of the `𝓛̄_t` on `Δ_X × Δ_Y` (`IsLipschitzPayoff`, the `ℓ₁` norm of the stacked
vector) with `0 < G_𝓛̄ ≤ 1`: the least such constant is at most `1` because the entries lie in
`[−1, 1]` (the proof, pp.18–19), and it must be positive for `η = √T/G_𝓛̄` to be defined. `T ≥ 1`
because Algorithm 3 needs `η > 0`. The final `= O(·) + o(1)·max{d₁, d₂}` line of the theorem is the
asymptotic reading of the explicit bound and is not restated. `ln` is `Real.log`. -/
theorem theorem_3 {d₁ d₂ : ℕ} (A : ℕ → Matrix (Fin d₁) (Fin d₂) ℝ) (Gbar η θ : ℝ) (T : ℕ)
    (x : ℕ → PiLp 1 (fun _ : Fin d₁ => ℝ)) (y : ℕ → PiLp 1 (fun _ : Fin d₂ => ℝ))
    (hT : 1 ≤ T)
    (hA : ∀ t ∈ Finset.Icc 1 T, ∀ i j, |A t i j| ≤ 1)
    (hGpos : 0 < Gbar) (hGle : Gbar ≤ 1)
    (hlip : ∀ t ∈ Finset.Icc 1 T,
      IsLipschitzPayoff (restrictedSimplex d₁ 0) (restrictedSimplex d₂ 0) Gbar (bilinearPayoff A t))
    (hη : η = Real.sqrt T / Gbar) (hθ : θ = Real.exp (-(η * Gbar)))
    (hθd : θ ≤ min (1 / (d₁ : ℝ)) (1 / (d₂ : ℝ)))
    (hrun : IsSPFTLRun
      (regularizedPayoff (bilinearPayoff A) (entropicRegularizer d₁) (entropicRegularizer d₂) η)
      (restrictedSimplex d₁ θ) (restrictedSimplex d₂ θ) T x y) :
    spRegret (bilinearPayoff A) (restrictedSimplex d₁ 0) (restrictedSimplex d₂ 0) T x y ≤
      32 * Gbar * Real.sqrt T * (1 + Real.log T) +
        2 * Real.sqrt T * max (Real.log d₁) (Real.log d₂) +
        2 * max (d₁ : ℝ) (d₂ : ℝ) * Gbar * T * Real.exp (-Real.sqrt T) := by sorry

end OnlineSaddlePoint.Supplement
