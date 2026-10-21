-- Prove2me | Theorems.Thm_NaiveFS_Multinomial_claim_w_ge_v
-- name    : NaiveFS.Multinomial.claim_w_ge_v
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T09:15:44.178133+00:00
-- url     : https://prove2.me/theorems/ecd79751-01a7-4c52-942b-91e8aad99fcd
-- title:
--   §3.4, pp. 7–8 — w(µ) ≥ v(µ) for every µ = (µ⁺, µ⁻) > 0
-- statement:
--   Let $f^+,f^-\in\mathbb R^m$ with $f^+_i,f^-_i>0$. For $\mu=(\mu^+,\mu^-)$ with $\mu^+,\mu^->0$ define
--   $$v_i(\mu)=(f^+_i+f^-_i)\log\frac{f^+_i+f^-_i}{\mu^++\mu^-},\qquad w_i(\mu)=f^+_i\log\frac{f^+_i}{\mu^+}+f^-_i\log\frac{f^-_i}{\mu^-}.$$
--   Then for every $i$,
--   $$w_i(\mu)\ge v_i(\mu).$$
--
--   This inequality lets the paper replace $\max(v_i(\mu),w_i(\mu)-\lambda)$ in (17) by $v_i(\mu)+\max(0,w_i(\mu)-v_i(\mu)-\lambda)$ and so reach the top-$k$ form of (USMNB). At $\mu=(\alpha,1-\alpha)$ it says $h(\alpha)\ge0$ for $\alpha\in(0,1)$.
-- source:
--   Askari, d'Aspremont & El Ghaoui, Naive Feature Selection, arXiv:1905.09884v4, pp. 7–8, §3.4, claim w(µ) ≥ v(µ) (after (17))

import Mathlib
import Definitions.Def_NaiveFS_Multinomial_Model
import Definitions.Def_NaiveFS_Multinomial_Dual

namespace NaiveFS.Multinomial

/-- §3.4, pp. 7–8: `w(µ) ≥ v(µ)` entrywise for every `µ = (µ⁺, µ⁻) > 0`, where
`vᵢ(µ) = (f⁺ᵢ + f⁻ᵢ) log((f⁺ᵢ + f⁻ᵢ)/(µ⁺ + µ⁻))` and
`wᵢ(µ) = f⁺ᵢ log(f⁺ᵢ/µ⁺) + f⁻ᵢ log(f⁻ᵢ/µ⁻)`, with `f± > 0` as in (14). -/
theorem claim_w_ge_v {m : ℕ} (fp fm : Fin m → ℝ) (hfp : ∀ i, 0 < fp i) (hfm : ∀ i, 0 < fm i)
    (mup mum : ℝ) (hmup : 0 < mup) (hmum : 0 < mum) (i : Fin m) :
    vmu fp fm mup mum i ≤ wmu fp fm mup mum i := by sorry

end NaiveFS.Multinomial
