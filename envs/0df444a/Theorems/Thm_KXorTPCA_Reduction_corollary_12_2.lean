-- Prove2me | Theorems.Thm_KXorTPCA_Reduction_corollary_12_2
-- name    : KXorTPCA.Reduction.corollary_12_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T17:24:49.295969+00:00
-- url     : https://prove2.me/theorems/63211f89-12c5-45b9-a553-daf153ddcd06
-- title:
--   Corollary 12.2 — reduction to Tensor PCA density for k′ < τ_{ρ,η/k}·k (k′ even) or τ_{ρ,η/k}/2·k (k′ odd)
-- statement:
--   Let $\rho\in(0,1]$, $k\ge1$ and $0\le\eta\le(k-2)/2$. With
--
--   $$\tau_{\rho,\eta/k}=\begin{cases}2\rho,&\rho\in(0,1/3),\\ 1-\rho,&\rho\in[1/3,3/5),\\ (1+\rho)/4,&\rho\in[3/5,1],\end{cases}\qquad\text{(Eq. (45))}$$
--
--   if $k'>0$ satisfies $k'<\tau_{\rho,\eta/k}\cdot k$ ($k'$ even) or $k'<\tau_{\rho,\eta/k}/2\cdot k$ ($k'$ odd), there is a polynomial-time average-case reduction (Definition C.6) for both detection and recovery from $k$-Gauss$_{\rho,\eta}(n)$ to $k'$-Gauss$_{\rho'=1,2\eta}(n')$ with $n'=n^{\Theta(1)}$.
--
--   Differences from the source:
--   - generalization: "$\eta,k\in\mathbb Z_+$" → $\eta$ real with $0\le\eta\le(k-2)/2$, $k\ge1$ integer; reason: integer $\eta$ is the special case; Eq. (45) and the surrounding text treat $\eta$ as real.
--   - reading: $n'=n^{\Theta(1)}$ → $\log n'_i/\log n_i\to c$ for some $c>0$; reason: Definition C.6.
--   - reading: "$k'$ satisfies …" → $k'>0$; reason: tensor orders are positive.
--   - reading: "poly-time average-case reduction for both detection and recovery" → the mission's Definition C.6; reason: Definitions C.5/C.6 leave these choices open.
-- source:
--   G. Bresler, A. Harbuzova, Average-Case Reductions for k-XOR and Tensor PCA, arXiv:2601.19016 (copy sha256 6ec029a7…), pp. 65–66 (PDF 68–69), Corollary 12.2, Eq. (45)

import Mathlib
import Definitions.Def_KXorTPCA_Reduction_Reductions

namespace KXorTPCA.Reduction

theorem corollary_12_2 :
    ∀ ρ : ℝ, 0 < ρ → ρ ≤ 1 → ∀ k : ℕ, 1 ≤ k → ∀ η : ℝ, 0 ≤ η → η ≤ ((k : ℝ) - 2) / 2 →
    ∀ k' : ℕ, 0 < k' →
      ((Even k' ∧ (k' : ℝ) <
          (if ρ < 1 / 3 then 2 * ρ else if ρ < 3 / 5 then 1 - ρ else (1 + ρ) / 4) * k) ∨
       (Odd k' ∧ (k' : ℝ) <
          (if ρ < 1 / 3 then 2 * ρ else if ρ < 3 / 5 then 1 - ρ else (1 + ρ) / 4) / 2 * k)) →
      AvgReduces (kModel (Choices.std .gauss) k) (ρ, η)
        (kModel (Choices.std .gauss) k') (1, 2 * η) anyDims anySig := by sorry

end KXorTPCA.Reduction
