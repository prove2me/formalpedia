-- Prove2me | Theorems.Thm_MultiNashRepair_proposition_4_5_of_one_lt_sigma
-- name    : MultiNashRepair.proposition_4_5_of_one_lt_sigma
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-26T23:46:39.128083+00:00
-- url     : https://prove2.me/theorems/00818289-580e-41a8-b343-0a273d045225
-- title:
--   Proposition 4.5 — uniform progress of $\widehat\Phi_u$ in both branches (with $\sigma>1$)
-- statement:
--   **Proposition 4.5 (Uniform Progress in Both Branches)**, with the paper's standing assumption $\sigma>1$.
--
--   Fix a rational target $\sigma$ with $\sigma>1$ and admissible controls for it: a reserve $d>0$ with $\sigma+8d<\sigma_\star$, an activation fraction $f_0\in[7/12,3/5]$ with $\sigma+7d<U(f_0)$ and $\sigma+7d<1/f_0$, step sizes $u=\tfrac12\min\{1/144,d/100\}$ and $\eta=\tfrac12\min\{1/4,d/24\}$, and a cutoff $m_0$. Let $m\ge m_0$, and let $(\varsigma,H)$ be a scalar state with $\varsigma<\sigma$ and $0<H\le L_0$. Put $\mu=S_u(H)-\varsigma-d$ and
--   $$\widehat\Phi_u(\varsigma,H)=\frac{\varsigma-G_0+2d}{H}+(1-a_u)\log\frac{H}{f_0}+a_u\log(1+QH).$$
--
--   1. **Descent branch.** If $0\le Z\le1$, $1-\eta Z\le P\le1$, $\varsigma^+\ge P\,[(1+\eta Z)\varsigma+\eta\mu]$ and $H^+=PH$, then
--   $$H\bigl(\widehat\Phi_u(\varsigma^+,H^+)-\widehat\Phi_u(\varsigma,H)\bigr)\ge\frac{\eta d}{2}>0 .$$
--   2. **Repair branch.** If $0\le E\le120u/m$, $\varsigma^+\ge c\varsigma+D-E$ with $D=\beta(G_0+QH)$, and $H^+=c(H+t)$, then
--   $$H\bigl(\widehat\Phi_u(\varsigma^+,H^+)-\widehat\Phi_u(\varsigma,H)\bigr)\ge 3d(1-c)>0 .$$
--
--   The potential $\widehat\Phi_u$ therefore increases by a fixed amount in both branches of Algorithm 1, which gives the iteration bound of Proposition 4.6.
--
--   **Formalization Note.** This is the statement of the milestone `MultiNashRepair.proposition_4_5` with the extra hypothesis $1<\sigma$. That milestone omits the hypothesis and is false without it: for $\sigma=-100$ and $d=10$ the admissibility conditions hold but $d>S_u(H)$, and the descent step with $Z=P=1$ decreases $\widehat\Phi_u$. The paper fixes $\sigma\in(1,\sigma_\star)$ throughout, which forces $d<1/8$.
-- source:
--   Tang, Ding, Fang, Breaking the One-Player Extension Barrier, arXiv:2611.06076, Proposition 4.5, p.14 (proof §5.5, p.39; potential (4.11)/(5.51)); standing assumption σ ∈ (1, σ⋆) of Theorem 1.1 and §3.3

import Mathlib
import Definitions.Def_MultiNashRepair_Controls

namespace MultiNashRepair

theorem proposition_4_5_of_one_lt_sigma {σ : ℚ} (ctrl : Controls σ) (hσ1 : 1 < σ) {m : ℕ}
    (hm : ctrl.m0 ≤ m) (ς H : ℝ) (hH0 : 0 < H) (hHL : H ≤ ctrl.knobs.L0) (hς : ς < σ) :
    let k := ctrl.knobs
    let d : ℝ := ctrl.d
    let η : ℝ := ctrl.η
    let mu := ctrl.mu ς H
    (∀ Z P ς' H' : ℝ, 0 ≤ Z → Z ≤ 1 → 1 - η * Z ≤ P → P ≤ 1 →
      P * ((1 + η * Z) * ς + η * mu) ≤ ς' → H' = P * H →
      η * d / 2 ≤ H * (k.Phihat d ς' H' - k.Phihat d ς H)) ∧
    (∀ E ς' H' : ℝ, 0 ≤ E → E ≤ 120 * (ctrl.u : ℝ) / m →
      k.c * ς + k.Dsh H - E ≤ ς' → H' = k.c * (H + k.t) →
      3 * d * (1 - k.c) ≤ H * (k.Phihat d ς' H' - k.Phihat d ς H)) ∧
    0 < η * d / 2 ∧ 0 < 3 * d * (1 - k.c) := by sorry

end MultiNashRepair
