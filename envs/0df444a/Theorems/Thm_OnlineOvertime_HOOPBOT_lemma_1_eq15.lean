-- Prove2me | Theorems.Thm_OnlineOvertime_HOOPBOT_lemma_1_eq15
-- name    : OnlineOvertime.HOOPBOT.lemma_1_eq15
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T04:19:45.542731+00:00
-- url     : https://prove2.me/theorems/5d470239-b1e6-4a26-8332-ec09986373bb
-- title:
--   Proof of Lemma 1, (15), p. 20 — along Rule (I), x̃^(K1) + θ1 ≥ θ1·α^{Σ b/B}, hence x̃^(K1) > (α − 1)θ1
-- statement:
--   Let an instance satisfy the standing assumptions, let $\theta_1=\zeta/(\alpha-1)$, and fix a server-date $(i,t)$. Let $j_0<j_1<\dots<j_K$ be customers allocated to $(i,t)$, all on regular capacity, the last one being $K_1=j_K$. Let $x^{(0)}=0$ and
--   $$x^{(k+1)}=x^{(k)}\Big(1+\frac{b_{i,j_k}}{B_{i,t}}\Big)+\theta_1\frac{c_{i,j_k}}{B_{i,t}},\qquad k=0,\dots,K,$$
--   with $x^{(k)}<d_i$ for $k=0,\dots,K$ (so each of these customers was served by Updating Rule (I)); write $\tilde x^{(K_1)}=x^{(K+1)}$ for the Rule (I) value at iteration $K_1$ before the cap of Rule (II). If the regular capacity is exceeded, $\sum_{k=0}^{K}b_{i,j_k}>B_{i,t}$, then
--   $$\tilde x^{(K_1)}+\theta_1\ \ge\ \big(x^{(0)}+\theta_1\big)\,\alpha^{\sum_{k=0}^{K}b_{i,j_k}/B_{i,t}}\qquad\text{and}\qquad \tilde x^{(K_1)}>(\alpha-1)\,\theta_1 .$$
--
--   This is the growth estimate on the regular-capacity price from which both statements of Lemma 1 follow.
--
--   **Formalization Note** The statement is about the Rule (I) recursion along the customers allocated to $(i,t)$, abstracted from the full run of Algorithm 1; the hypothesis $x^{(k)}<d_i$ records that each update was a Rule (I) update (Step 6), as in the paper's setting.
-- source:
--   Keyvanshokooh, Shi, Van Oyen, Online Advance Scheduling with Overtime: A Primal-Dual Approach, accepted manuscript (MSOM, accepted May 2019; SSRN 3352166), p. 20, proof of Lemma 1, (15)

import Mathlib
import Definitions.Def_OnlineOvertime_HOOPBOT_Model

namespace OnlineOvertime.HOOPBOT

/-- Proof of Lemma 1, (15), p. 20. Same setting as `lemma_1`: along the regular-capacity
allocations `js 0 < … < js K` to server-date `(i, t)`, the price follows Updating Rule (I)
with `θ1 = ζ/(α − 1)` from `x 0 = 0`, and the regular capacity is exceeded. Then
`x̃^{(K₁)} + θ1 ≥ (x^{(0)} + θ1) α^{Σ_k b_{i,js k}/B_{i,t}}` and `x̃^{(K₁)} > (α − 1) θ1`. -/
theorem lemma_1_eq15 {n T m : ℕ} (I : Instance n T m) (hS : I.Standing)
    (i : Fin n) (t : Fin T) (K : ℕ) (js : Fin (K + 1) → Fin m) (hjs : StrictMono js)
    (x : ℕ → ℝ) (hx0 : x 0 = 0)
    (hx : ∀ k : Fin (K + 1), x (k.val + 1) =
      x k.val * (1 + I.b (js k) i / I.B i t) + thetaOne I * (I.c (js k) i / I.B i t))
    (hreg : ∀ k : Fin (K + 1), x k.val < I.d i)
    (hload : I.B i t < ∑ k, I.b (js k) i) :
    (x 0 + thetaOne I) * alpha I ^ (∑ k, I.b (js k) i / I.B i t) ≤ x (K + 1) + thetaOne I ∧
    (alpha I - 1) * thetaOne I < x (K + 1) := by sorry

end OnlineOvertime.HOOPBOT
