-- Prove2me | Theorems.Thm_LeaseModular_JointChoice_pi_LI_closed_form
-- name    : LeaseModular.JointChoice.pi_LI_closed_form
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-18T22:11:25.34032+00:00
-- url     : https://prove2.me/theorems/842cd399-98d4-408a-8c69-819c05a674e2
-- title:
--   Proof of Lemma 2, p. 34 — optimal profit of leasing an integral product, with disposal of off-lease products iff c < C_LI
-- statement:
--   Throughout, $\delta_1,\delta_2$ are the module durabilities under selling, $\gamma>0$ the relative return condition of off-lease modules (durabilities under leasing $\delta_{kl}=\gamma\delta_k$), and $c$ the per-module production cost, subject to the standing assumptions $0<\delta_2<\delta_1<1$, $\gamma\delta_1<1$, $0<c<(1-\delta_2)/2$ and $c<(1-\gamma\delta_2)/2$.
--
--   When the firm leases an integral product, write $a=\delta_1+\delta_2$ and $C_{LI}=(2-\gamma a)/8$.
--
--   1. If $c<C_{LI}$, the optimal profit is
--   $$\Pi^*_{LI}=\frac{(2-\gamma a)(1-4c)+8c^2}{4\,(2-\gamma a)},$$
--   and every optimal decision satisfies $0<L_u<L_n$ (some off-lease products are removed from the market).
--   2. If $c\ge C_{LI}$, the optimal profit is
--   $$\Pi^*_{LI}=\frac{(2-4c+\gamma a)^2}{8\,(2+3\gamma a)},$$
--   and every optimal decision satisfies $0<L_u=L_n$ (all off-lease products are re-leased).
--
--   This is the leasing benchmark against which modularity under leasing (Lemma 2) and selling (Lemma 3) are compared.
-- source:
--   Agrawal, Atasu & Ülkü, Leasing, Modularity, and the Circular Economy, author manuscript (Management Science, doi:10.1287/mnsc.2020.3829), proof of Lemma 2, Appendix p. 34 (Π*_LI and C_LI)

import Mathlib
import Definitions.Def_LeaseModular_JointChoice_Setting

namespace LeaseModular.JointChoice

/-- Proof of Lemma 2, Appendix p. 34: the optimal LI profit. With `a = δ₁ + δ₂`:
* if `c < C_LI(δ₁, δ₂, γ)`, then `Π*_LI = ((2 − γa)(1 − 4c) + 8c²)/(4(2 − γa))` and every optimal
  decision has `0 < L_u < L_n`;
* otherwise `Π*_LI = (2 − 4c + γa)²/(8(2 + 3γa))` and every optimal decision has `0 < L_u = L_n`. -/
theorem pi_LI_closed_form (P : Params) (hP : Standing P) :
    (P.c < CLI P.δ₁ P.δ₂ P.γ →
      IsOptLI P (((2 - P.γ * (P.δ₁ + P.δ₂)) * (1 - 4 * P.c) + 8 * P.c ^ 2) /
        (4 * (2 - P.γ * (P.δ₁ + P.δ₂)))) ∧
      ∀ x, IsMaxLI P x → 0 < x.u ∧ x.u < x.n) ∧
    (CLI P.δ₁ P.δ₂ P.γ ≤ P.c →
      IsOptLI P ((2 - 4 * P.c + P.γ * (P.δ₁ + P.δ₂)) ^ 2 /
        (8 * (2 + 3 * P.γ * (P.δ₁ + P.δ₂)))) ∧
      ∀ x, IsMaxLI P x → 0 < x.u ∧ x.u = x.n) := by sorry

end LeaseModular.JointChoice
