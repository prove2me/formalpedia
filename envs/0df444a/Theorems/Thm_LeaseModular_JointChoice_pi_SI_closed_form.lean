-- Prove2me | Theorems.Thm_LeaseModular_JointChoice_pi_SI_closed_form
-- name    : LeaseModular.JointChoice.pi_SI_closed_form
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-18T22:11:22.160644+00:00
-- url     : https://prove2.me/theorems/4189d529-2e31-45fb-8d11-b383e3ba3746
-- title:
--   Proof of Lemma 1, p. 31 — the optimal profit of selling an integral product is (2−4c+δ1+δ2)²/(8(2+3(δ1+δ2)))
-- statement:
--   Throughout, $\delta_1,\delta_2$ are the module durabilities under selling, $\gamma>0$ the relative return condition of off-lease modules (durabilities under leasing $\delta_{kl}=\gamma\delta_k$), and $c$ the per-module production cost, subject to the standing assumptions $0<\delta_2<\delta_1<1$, $\gamma\delta_1<1$, $0<c<(1-\delta_2)/2$ and $c<(1-\gamma\delta_2)/2$.
--
--   When the firm sells an integral product, the optimal profit of the problem $\max_{S_n\ge0}\Pi_{SI}(S_n)=(p_n(S_n)-2c)S_n$ is
--   $$\Pi^*_{SI}=\frac{(2-4c+\delta_1+\delta_2)^2}{8\,(2+3(\delta_1+\delta_2))},$$
--   and it is attained exactly at
--   $$S^*_n=\frac{2-4c+\delta_1+\delta_2}{2\,(2+3(\delta_1+\delta_2))}.$$
--
--   This is the baseline profit against which every other combination of business model and architecture is compared.
--
--   **Formalization Note.** The inverse demand uses $-2S_n(\delta_1+\delta_2)$ in place of the printed $-2S_n(1+\delta_1+\delta_2)$ (see the Setting definition); the printed $S^*_n$ and $\Pi^*_{SI}$ belong to the corrected form. "Attained exactly at" is stated as: a feasible $S_n$ reaches the optimal value if and only if $S_n=S^*_n$.
-- source:
--   Agrawal, Atasu & Ülkü, Leasing, Modularity, and the Circular Economy, author manuscript (Management Science, doi:10.1287/mnsc.2020.3829), proof of Lemma 1, Appendix p. 31 (S*_n and Π*_SI)

import Mathlib
import Definitions.Def_LeaseModular_JointChoice_Setting

namespace LeaseModular.JointChoice

/-- Proof of Lemma 1, Appendix p. 31: under the standing assumptions the SI problem
`max_{S_n ≥ 0} (p_n(S_n) − 2c) S_n` has optimal value
`Π*_SI = (2 − 4c + δ₁ + δ₂)² / (8(2 + 3(δ₁ + δ₂)))`, attained exactly at
`S*_n = (2 − 4c + δ₁ + δ₂)/(2(2 + 3(δ₁ + δ₂)))`. -/
theorem pi_SI_closed_form (P : Params) (hP : Standing P) :
    IsOptSI P ((2 - 4 * P.c + P.δ₁ + P.δ₂) ^ 2 / (8 * (2 + 3 * (P.δ₁ + P.δ₂)))) ∧
      ∀ S ∈ feasSI,
        profitSI P S = (2 - 4 * P.c + P.δ₁ + P.δ₂) ^ 2 / (8 * (2 + 3 * (P.δ₁ + P.δ₂))) ↔
          S = (2 - 4 * P.c + P.δ₁ + P.δ₂) / (2 * (2 + 3 * (P.δ₁ + P.δ₂))) := by sorry

end LeaseModular.JointChoice
