-- Prove2me | Theorems.Thm_OnlineOvertime_HOOPBOT_lemma_1
-- name    : OnlineOvertime.HOOPBOT.lemma_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T04:19:46.749245+00:00
-- url     : https://prove2.me/theorems/896ed6d1-b398-4126-8e41-649fc40b9eb7
-- title:
--   Lemma 1, p. 20 — with θ1 = ζ/(α − 1), overrunning regular capacity pushes x̃^(K1) above d_i, or prices customer K1 out
-- statement:
--   Let an instance satisfy the standing assumptions, let $\theta_1=\zeta/(\alpha-1)$ with $\zeta=\min(d_{\max},\gamma_{\max})$, and fix a server-date $(i,t)$. Let $j_0<j_1<\dots<j_K$ be customers allocated to $(i,t)$ on regular capacity, the last one being $K_1=j_K$, so that the regular-capacity price follows Updating Rule (I): $x^{(0)}=0$,
--   $$x^{(k+1)}=x^{(k)}\Big(1+\frac{b_{i,j_k}}{B_{i,t}}\Big)+\theta_1\frac{c_{i,j_k}}{B_{i,t}},\qquad x^{(k)}<d_i\quad(k=0,\dots,K),$$
--   and let $\tilde x^{(K_1)}=x^{(K+1)}$ be the Rule (I) value at iteration $K_1$ before the cap. If $\sum_{k=0}^{K}b_{i,j_k}>B_{i,t}$, then
--
--   1. (13) if $d_i\le\gamma_{\max}$, then $\tilde x^{(K_1)}>d_i$;
--   2. (14) if $d_i>\gamma_{\max}$, then $c_{i,K_1}-b_{i,K_1}\tilde x^{(K_1)}<0$.
--
--   So once the regular capacity of $(i,t)$ is used up, either further customers at $(i,t)$ are served on overtime or none is served there at all.
--
--   **Formalization Note** The statement is about the Rule (I) recursion along the customers allocated to $(i,t)$, abstracted from the run of Algorithm 1; the hypothesis $x^{(k)}<d_i$ records that each of these updates was a Rule (I) update (Step 6), which is the setting of "regular capacity usage only".
-- source:
--   Keyvanshokooh, Shi, Van Oyen, Online Advance Scheduling with Overtime: A Primal-Dual Approach, accepted manuscript (MSOM, accepted May 2019; SSRN 3352166), p. 20, Lemma 1, (13)–(14)

import Mathlib
import Definitions.Def_OnlineOvertime_HOOPBOT_Model

namespace OnlineOvertime.HOOPBOT

/-- Lemma 1 (13)–(14), p. 20. Fix a server-date `(i, t)` and let `js 0 < … < js K` be the
customers allocated to it up to iteration `K₁ = js K`, every one of them on regular capacity
(the price `x k` before the `k`-th of these allocations is below `d_i`), so that `x` follows
Updating Rule (I) with `θ1 = ζ/(α − 1)` from `x 0 = 0`; `x (K + 1)` is the Rule (I) value
`x̃^{(K₁)}` before the cap (II). If the regular capacity is exceeded,
`Σ_k b_{i,js k} > B_{i,t}`, then `x̃^{(K₁)} > d_i` when `d_i ≤ γmax` (13), and
`c_{i,K₁} − b_{i,K₁} x̃^{(K₁)} < 0` when `d_i > γmax` (14). -/
theorem lemma_1 {n T m : ℕ} (I : Instance n T m) (hS : I.Standing)
    (i : Fin n) (t : Fin T) (K : ℕ) (js : Fin (K + 1) → Fin m) (hjs : StrictMono js)
    (x : ℕ → ℝ) (hx0 : x 0 = 0)
    (hx : ∀ k : Fin (K + 1), x (k.val + 1) =
      x k.val * (1 + I.b (js k) i / I.B i t) + thetaOne I * (I.c (js k) i / I.B i t))
    (hreg : ∀ k : Fin (K + 1), x k.val < I.d i)
    (hload : I.B i t < ∑ k, I.b (js k) i) :
    (I.d i ≤ gammaMax I → I.d i < x (K + 1)) ∧
    (gammaMax I < I.d i →
      I.c (js (Fin.last K)) i - I.b (js (Fin.last K)) i * x (K + 1) < 0) := by sorry

end OnlineOvertime.HOOPBOT
