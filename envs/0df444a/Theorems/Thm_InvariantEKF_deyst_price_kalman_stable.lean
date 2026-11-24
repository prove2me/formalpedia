-- Prove2me | Theorems.Thm_InvariantEKF_deyst_price_kalman_stable
-- name    : InvariantEKF.deyst_price_kalman_stable
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-24T01:19:01.420264+00:00
-- url     : https://prove2.me/theorems/582329f2-3c39-47df-b550-011aade24d75
-- title:
--   Theorem 3 (Deyst and Price, 1968; as corrected): stability of the linear Kalman filter
-- statement:
--   Consider the linear system $\dot x_t=A_tx_t$, $t\ge0$, observed through $y_{t_n}=Hx_{t_n}$ at the times $t_n=n\,\Delta t$. Let $\Phi_s^t$ be its transition matrix. Assume there are constants $\alpha_1,\alpha_2,\beta_1,\beta_2,\delta_1,\delta_2,\delta_3>0$ and $M\ge1$ such that:
--
--   1. $(\Phi_{t_n}^{t_{n+1}})^T\Phi_{t_n}^{t_{n+1}}\succeq\delta_1I$ for all $n$;
--   2. there are $q\ge1$ and $Q'\succeq\delta_2I_q$ with $Q_s=G_sQ'G_s^T$ for some $G_s\in\mathbb R^{p\times q}$, for every $s>0$;
--   3. $N_n\succeq\delta_3I$ for all $n\ge1$;
--   4. $\alpha_1I\preceq\int_{t_{n-M}}^{t_n}\Phi_s^{t_n}Q_s(\Phi_s^{t_n})^T\,ds\preceq\alpha_2I$ for all $n\ge M$, the integrand being integrable;
--   5. $\beta_1I\preceq\sum_{i=n-M}^{n}(\Phi_{t_n}^{t_i})^TH^TN_i^{-1}H\,\Phi_{t_n}^{t_i}\preceq\beta_2I$ for all $n\ge M+1$;
--   6. $(\Phi_s^t)^T\Phi_s^t\preceq cI$ whenever $s,t$ lie in one sampling interval $[t_n,t_{n+1}]$.
--
--   Let the Kalman filter tuned with $Q$ and $N$ start at time $t_0\ge0$ from any $\hat x_{t_0}$ and any $P_{t_0}\succ0$. Then there exist $\gamma_{\min},\gamma_{\max}>0$ with $\gamma_{\min}I\preceq P_t\preceq\gamma_{\max}I$ for all $t\ge t_0$. Moreover there are $C$ and $r>0$ with
--
--   $$(\hat x_t-x_t)^TP_t^{-1}(\hat x_t-x_t)\le C\,e^{-r(t-t_0)}\qquad(t\ge t_0),$$
--
--   and $\|\hat x_t-x_t\|\to0$ as $t\to\infty$.
--
--   **Formalization Note** The theorem is cited from Deyst and Price (1968). Condition 5 is printed in the paper as $\sum_{i=n-M}^{n-1}(\Phi_{t_{i+1}}^{t_n})^TH^TN_n^{-1}H\Phi_{t_{i+1}}^{t_n}$; it is stated here in the form of Deyst and Price, with the backward transition $\Phi_{t_n}^{t_i}$ and $N_i$. The paper writes "$\succeq 0$" for the constants; they are taken strictly positive. Condition 6 is not in the paper. Without it the bound "$P_t\preceq\gamma_{\max}I$ for all $t$" fails between observation times (see the report).
-- source:
--   Barrau and Bonnabel, The invariant extended Kalman filter as a stable observer, arXiv:1410.1465v4 (2015), Section 3.4, Theorem 3, p. 13; conditions (iv)-(v) in the form of Deyst and Price (1968)

import Mathlib
import Definitions.Def_InvariantEKF_Basic

open MeasureTheory Matrix Filter Topology

namespace InvariantEKF

theorem deyst_price_kalman_stable {d : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : ℝ → Matrix (Fin d) (Fin d) ℝ) (H : Matrix ι (Fin d) ℝ)
    (Phi : ℝ → ℝ → Matrix (Fin d) (Fin d) ℝ) (hPhi : IsTransitionMatrix A Phi)
    (Q : ℝ → Matrix (Fin d) (Fin d) ℝ) (Nm : ℕ → Matrix ι ι ℝ) (dt : ℝ) (hdt : 0 < dt)
    (α₁ α₂ β₁ β₂ δ₁ δ₂ δ₃ c : ℝ) (M : ℕ) (hα₁ : 0 < α₁) (hα₂ : 0 < α₂) (hβ₁ : 0 < β₁)
    (hβ₂ : 0 < β₂) (hδ₁ : 0 < δ₁) (hδ₂ : 0 < δ₂) (hδ₃ : 0 < δ₃) (hM : 1 ≤ M)
    (hDP : DeystPriceConditions dt Phi Q H Nm α₁ α₂ β₁ β₂ δ₁ δ₂ δ₃ M)
    (hbdd : BoundedTransition dt Phi c)
    (x : ℝ → Fin d → ℝ) (hx : ∀ t, 0 ≤ t → HasDerivWithinAt x (A t *ᵥ x t) (Set.Ici 0) t)
    (t0 : ℝ) (ht0 : 0 ≤ t0) (xhat0 : Fin d → ℝ)
    (P0 : Matrix (Fin d) (Fin d) ℝ) (hP0 : P0.PosDef)
    (xs : ℕ → ℝ → Fin d → ℝ) (Ps : ℕ → ℝ → Matrix (Fin d) (Fin d) ℝ)
    (hrun : IsKalmanRun A H Q Nm dt x t0 xhat0 P0 xs Ps) :
    ∃ γmin γmax : ℝ, 0 < γmin ∧ 0 < γmax ∧
      (∀ t, t0 ≤ t → LoewnerLE (γmin • (1 : Matrix (Fin d) (Fin d) ℝ)) (piecewiseRun Ps dt t) ∧
        LoewnerLE (piecewiseRun Ps dt t) (γmax • 1)) ∧
      (∃ C r : ℝ, 0 < r ∧ ∀ t, t0 ≤ t →
        (piecewiseRun xs dt t - x t) ⬝ᵥ ((piecewiseRun Ps dt t)⁻¹ *ᵥ (piecewiseRun xs dt t - x t)) ≤
          C * Real.exp (-r * (t - t0))) ∧
      Tendsto (fun t => ‖piecewiseRun xs dt t - x t‖) atTop (𝓝 0) := by sorry

end InvariantEKF
