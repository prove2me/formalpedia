-- Prove2me | Theorems.Thm_LeaseModular_JointChoice_lemma_2
-- name    : LeaseModular.JointChoice.lemma_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-18T22:11:32.273887+00:00
-- url     : https://prove2.me/theorems/7ffdd12d-d9d1-435b-8d46-914311b20459
-- title:
--   Lemma 2, p. 13 — under leasing, modularity is strictly more profitable (and L_un > 0) iff c < C_LM2(δ1,δ2,γ), corrected
-- statement:
--   Throughout, $\delta_1,\delta_2$ are the module durabilities under selling, $\gamma>0$ the relative return condition of off-lease modules (durabilities under leasing $\delta_{kl}=\gamma\delta_k$), and $c$ the per-module production cost, subject to the standing assumptions $0<\delta_2<\delta_1<1$, $\gamma\delta_1<1$, $0<c<(1-\delta_2)/2$ and $c<(1-\gamma\delta_2)/2$.
--
--   Under leasing, with $C_{LM1}=\frac{1-\gamma\delta_1}{4}$, $C_{LI}=\frac{2-\gamma(\delta_1+\delta_2)}{8}$ and $C_{LM2}=\frac{(1-\gamma\delta_2)(\delta_1+\delta_2)}{3\delta_1+5\delta_2}$, the optimal profits $\Pi^*_{LM}$ and $\Pi^*_{LI}$ exist and
--   $$\Big(\Pi^*_{LM}>\Pi^*_{LI}\ \text{and every optimal LM decision has } L_{un}>0\Big)\iff c<C_{LM2}.$$
--   Moreover:
--
--   1. $C_{LM2}$ is strictly increasing in $\delta_1$ on $\{\delta_1\in(\delta_2,1):\gamma\delta_1<1\}$ and strictly decreasing in $\delta_2$ on $(0,\delta_1)$;
--   2. $c<C_{LM2}$ if and only if $\delta_2<D_L(\delta_1,\gamma,c)=\frac1{2\gamma}\big(1-5c-\gamma\delta_1+\sqrt{25c^2+(1+\gamma\delta_1)^2-2c(5+\gamma\delta_1)}\big)$;
--   3. if $c<C_{LM1}$, every optimal LM decision satisfies $L_{uu}+L_{un}<L_{nn}$ (the supply constraint of the more durable module is slack);
--   4. $C_{LM1}<C_{LI}<C_{LM2}$.
--
--   A leasing firm uses modularity — leasing blended products with a reused durable module and a new less durable one — only when production is cheap enough.
--
--   **Formalization Note.** $C_{LM2}$ is the corrected threshold (the paper prints an extra factor $\gamma$ in the denominator, under which this lemma is false for $\gamma\ne1$). "$L_{un}>0$" and "the constraint is not binding" are stated for every optimal decision.
-- source:
--   Agrawal, Atasu & Ülkü, Leasing, Modularity, and the Circular Economy, author manuscript (Management Science, doi:10.1287/mnsc.2020.3829), Lemma 2, p. 13 (proof: Appendix pp. 34–36)

import Mathlib
import Definitions.Def_LeaseModular_JointChoice_Setting

namespace LeaseModular.JointChoice

/-- Lemma 2, p. 13, with `C_LM2` in its corrected form. Under leasing, modularity gives strictly
higher profit and blended UN products are leased (`Π*_LM > Π*_LI`, and every optimal LM decision
has `L_un > 0`) if and only if `c < C_LM2(δ₁, δ₂, γ)`; `C_LM2` is strictly increasing in `δ₁`
(on `δ₁ ∈ (δ₂, 1)` with `γδ₁ < 1`) and strictly decreasing in `δ₂` (on `δ₂ ∈ (0, δ₁)`); the
condition `c < C_LM2` is equivalent to `δ₂ < D_L(δ₁, γ, c)`; if `c < C_LM1(δ₁, γ)` every optimal LM
decision has `L_uu + L_un < L_nn`; and `C_LM1 < C_LI < C_LM2`. -/
theorem lemma_2 (P : Params) (hP : Standing P) :
    (∃ vLM vLI : ℝ, IsOptLM P vLM ∧ IsOptLI P vLI ∧
      ((vLI < vLM ∧ ∀ x, IsMaxLM P x → 0 < x.un) ↔ P.c < CLM2 P.δ₁ P.δ₂ P.γ)) ∧
    StrictMonoOn (fun d => CLM2 d P.δ₂ P.γ) {d | P.δ₂ < d ∧ d < 1 ∧ P.γ * d < 1} ∧
    StrictAntiOn (fun d => CLM2 P.δ₁ d P.γ) (Set.Ioo 0 P.δ₁) ∧
    (P.c < CLM2 P.δ₁ P.δ₂ P.γ ↔ P.δ₂ < DL P.δ₁ P.γ P.c) ∧
    (P.c < CLM1 P.δ₁ P.γ → ∀ x, IsMaxLM P x → x.uu + x.un < x.nn) ∧
    CLM1 P.δ₁ P.γ < CLI P.δ₁ P.δ₂ P.γ ∧ CLI P.δ₁ P.δ₂ P.γ < CLM2 P.δ₁ P.δ₂ P.γ := by sorry

end LeaseModular.JointChoice
