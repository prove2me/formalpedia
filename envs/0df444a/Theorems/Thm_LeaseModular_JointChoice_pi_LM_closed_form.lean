-- Prove2me | Theorems.Thm_LeaseModular_JointChoice_pi_LM_closed_form
-- name    : LeaseModular.JointChoice.pi_LM_closed_form
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-18T22:11:32.605244+00:00
-- url     : https://prove2.me/theorems/3b0c0be4-adec-4fff-ac6b-02f37d9f691f
-- title:
--   Proof of Lemma 2, p. 35 (Cases 1, 2, 4) — optimal profit of leasing a modular product in the three cost regimes
-- statement:
--   Throughout, $\delta_1,\delta_2$ are the module durabilities under selling, $\gamma>0$ the relative return condition of off-lease modules (durabilities under leasing $\delta_{kl}=\gamma\delta_k$), and $c$ the per-module production cost, subject to the standing assumptions $0<\delta_2<\delta_1<1$, $\gamma\delta_1<1$, $0<c<(1-\delta_2)/2$ and $c<(1-\gamma\delta_2)/2$.
--
--   When the firm leases a modular product, with $C_{LM1}=(1-\gamma\delta_1)/4$ and $C_{LM2}=(1-\gamma\delta_2)(\delta_1+\delta_2)/(3\delta_1+5\delta_2)$, the optimal profit is:
--
--   1. for $c<C_{LM1}$,
--   $$\Pi^*_{LM}=\frac{(1-2c)^2-\gamma(\delta_1+\delta_2)(1-2c(2-c))+(1-4c)\gamma^2\delta_1\delta_2}{4(1-\gamma\delta_1)(1-\gamma\delta_2)};$$
--   2. for $C_{LM1}\le c<C_{LM2}$,
--   $$\Pi^*_{LM}=\frac{-8c(1-\gamma\delta_2)(1+\gamma(2\delta_1+3\delta_2))+4c^2(2+3\gamma(\delta_1+\delta_2))+(1-\gamma\delta_2)(2+\gamma(5\delta_1+7\delta_2+\gamma\delta_1(\delta_1+\delta_2)))}{8(1-\gamma\delta_2)(1+\gamma(3\delta_1+4\delta_2))};$$
--   3. for $c\ge C_{LM2}$,
--   $$\Pi^*_{LM}=\frac{(2-4c+\gamma(\delta_1+\delta_2))^2}{16+24\gamma(\delta_1+\delta_2)}.$$
--
--   The three regimes are the paper's Cases 1, 2 and 4 of the KKT analysis (Case 3 never occurs). In the last regime $\Pi^*_{LM}=\Pi^*_{LI}$.
--
--   **Formalization Note.** $C_{LM2}$ is used in its corrected form, without the factor $\gamma$ the paper prints in the denominator (see the Setting definition).
-- source:
--   Agrawal, Atasu & Ülkü, Leasing, Modularity, and the Circular Economy, author manuscript (Management Science, doi:10.1287/mnsc.2020.3829), proof of Lemma 2, Appendix p. 35, Cases 1, 2 and 4 (Π*_LM, C_LM1, C_LM2), summarized at the top of p. 36

import Mathlib
import Definitions.Def_LeaseModular_JointChoice_Setting

namespace LeaseModular.JointChoice

/-- Proof of Lemma 2, Appendix p. 35 (Cases 1, 2 and 4): the optimal LM profit in three regimes,
with `C_LM2` in its corrected form `(1 − γδ₂)(δ₁ + δ₂)/(3δ₁ + 5δ₂)`.
* `c < C_LM1`: `Π*_LM = ((1−2c)² − γ(δ₁+δ₂)(1 − 2c(2−c)) + (1−4c)γ²δ₁δ₂)/(4(1−γδ₁)(1−γδ₂))`;
* `C_LM1 ≤ c < C_LM2`: `Π*_LM = (−8c(1−γδ₂)(1+γ(2δ₁+3δ₂)) + 4c²(2+3γ(δ₁+δ₂))
  + (1−γδ₂)(2+γ(5δ₁+7δ₂+γδ₁(δ₁+δ₂))))/(8(1−γδ₂)(1+γ(3δ₁+4δ₂)))`;
* `C_LM2 ≤ c`: `Π*_LM = (2 − 4c + γ(δ₁+δ₂))²/(16 + 24γ(δ₁+δ₂))`. -/
theorem pi_LM_closed_form (P : Params) (hP : Standing P) :
    (P.c < CLM1 P.δ₁ P.γ →
      IsOptLM P (((1 - 2 * P.c) ^ 2 - P.γ * (P.δ₁ + P.δ₂) * (1 - 2 * P.c * (2 - P.c)) +
          (1 - 4 * P.c) * P.γ ^ 2 * P.δ₁ * P.δ₂) /
        (4 * (1 - P.γ * P.δ₁) * (1 - P.γ * P.δ₂)))) ∧
    (CLM1 P.δ₁ P.γ ≤ P.c → P.c < CLM2 P.δ₁ P.δ₂ P.γ →
      IsOptLM P ((-8 * P.c * (1 - P.γ * P.δ₂) * (1 + P.γ * (2 * P.δ₁ + 3 * P.δ₂)) +
          4 * P.c ^ 2 * (2 + 3 * P.γ * (P.δ₁ + P.δ₂)) +
          (1 - P.γ * P.δ₂) *
            (2 + P.γ * (5 * P.δ₁ + 7 * P.δ₂ + P.γ * P.δ₁ * (P.δ₁ + P.δ₂)))) /
        (8 * (1 - P.γ * P.δ₂) * (1 + P.γ * (3 * P.δ₁ + 4 * P.δ₂))))) ∧
    (CLM2 P.δ₁ P.δ₂ P.γ ≤ P.c →
      IsOptLM P ((2 - 4 * P.c + P.γ * (P.δ₁ + P.δ₂)) ^ 2 /
        (16 + 24 * P.γ * (P.δ₁ + P.δ₂)))) := by sorry

end LeaseModular.JointChoice
