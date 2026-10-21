-- Prove2me | Theorems.Thm_NaiveFS_Multinomial_dual_identity
-- name    : NaiveFS.Multinomial.dual_identity
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T09:15:52.335998+00:00
-- url     : https://prove2.me/theorems/d5565306-5631-4928-9294-647dad15dab8
-- title:
--   §3.4, pp. 7–8 — the Lagrangian dual of (SMNB) equals −S + min (17), which equals ψ(k) = C + min_α s_k(h(α))
-- statement:
--   Let $f^\pm\in\mathbb R^m$ with $f^\pm_i>0$, $S=\mathbf 1^\top(f^++f^-)$, and $k<m$. Let
--   $$\Psi_{\mathrm L}(k)=\inf_{\mu^+,\mu^->0,\ \lambda\ge0}\ \sup_{\theta^+,\theta^->0}\ f^{+\top}\log\theta^++f^{-\top}\log\theta^-+\mu^+(1-\mathbf 1^\top\theta^+)+\mu^-(1-\mathbf 1^\top\theta^-)+\lambda\big(k-\|\theta^+-\theta^-\|_0\big)$$
--   be the Lagrangian dual value of (SMNB). Then
--   $$\Psi_{\mathrm L}(k)=-S+\inf_{\mu^+,\mu^->0,\ \lambda\ge0}\ \mu^++\mu^-+\lambda k+\sum_{i=1}^m\max\big(v_i(\mu),w_i(\mu)-\lambda\big)\qquad(17)$$
--   and the right-hand side equals
--   $$\psi(k)=C+\inf_{\alpha\in(0,1)}s_k\big(h(\alpha)\big),\qquad C=(f^++f^-)^\top\log(f^++f^-)-S\log S.$$
--
--   This identifies the relaxation (USMNB) as the Lagrangian dual of the sparse problem, which is what gives $\phi(k)\le\psi(k)$ by weak duality and what Theorem 3.6 compares against.
--
--   **Formalization Note** The page writes the inner maximum over $\theta^\pm\in[0,1]^m$. Its derivation, via the closed forms (15)–(16), ignores the bound $\theta\le1$, and with the box kept the dual value can be strictly smaller than $\psi(k)$ (for $f^+=(1000,1,1)$, $f^-=(1,1,3)$, $k=1$: below $-29.994$ against $\psi(1)\approx-29.988$). The statement therefore uses $\theta^\pm\in(0,\infty)^m$, which is the problem the page's computation actually solves. The multipliers range over $\mu^\pm>0$, as on the page after (15); for $\mu^\pm\le0$ the inner supremum is $+\infty$, so this does not change the infimum. $k<m$ is the standing assumption of §3.1.
-- source:
--   Askari, d'Aspremont & El Ghaoui, Naive Feature Selection, arXiv:1905.09884v4, pp. 7–8, §3.4, Lagrangian dual, (14)–(17), and the reduction to ψ(k) = C + min s_k(h(α))

import Mathlib
import Definitions.Def_NaiveFS_Multinomial_Model
import Definitions.Def_NaiveFS_Multinomial_Dual

namespace NaiveFS.Multinomial

/-- §3.4, pp. 7–8: the Lagrangian dual of (SMNB) equals `−S + min_{µ>0, λ≥0} (17)`, which
equals `ψ(k) = C + min_α s_k(h(α))` of (USMNB). The inner maximization is over
`θ± ∈ (0,∞)ᵐ` (see the item's note: with the page's box `[0,1]ᵐ` the identity fails). -/
theorem dual_identity {m : ℕ} (fp fm : Fin m → ℝ) (hfp : ∀ i, 0 < fp i) (hfm : ∀ i, 0 < fm i)
    (k : ℕ) (hkm : k < m) :
    dualValue fp fm k = -S fp fm + sInf {v | ∃ mup mum lam : ℝ, 0 < mup ∧ 0 < mum ∧ 0 ≤ lam ∧
        v = obj17 fp fm k mup mum lam} ∧
    -S fp fm + sInf {v | ∃ mup mum lam : ℝ, 0 < mup ∧ 0 < mum ∧ 0 ≤ lam ∧
        v = obj17 fp fm k mup mum lam} = psi fp fm k := by sorry

end NaiveFS.Multinomial
