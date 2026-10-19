-- Prove2me | Theorems.Thm_LeaseModular_JointChoice_proposition_3
-- name    : LeaseModular.JointChoice.proposition_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-18T22:12:10.862988+00:00
-- url     : https://prove2.me/theorems/f80ea7cb-1f7d-4912-9cf3-44849c8552a3
-- title:
--   Proposition 3, p. 17 — the firm leases a modular product iff c < C_M (γ ≤ 1) or c < C_LM2 (γ > 1); otherwise it sells modular/integral or leases integral
-- statement:
--   Throughout, $\delta_1,\delta_2$ are the module durabilities under selling, $\gamma>0$ the relative return condition of off-lease modules (durabilities under leasing $\delta_{kl}=\gamma\delta_k$), and $c$ the per-module production cost, subject to the standing assumptions $0<\delta_2<\delta_1<1$, $\gamma\delta_1<1$, $0<c<(1-\delta_2)/2$ and $c<(1-\gamma\delta_2)/2$.
--
--   Let $\Pi^*_{LM},\Pi^*_{SM},\Pi^*_{LI},\Pi^*_{SI}$ denote the optimal profits of leasing a modular product, selling a modular product, leasing an integral product and selling an integral product. All four exist, and the firm's joint choice of business model and architecture is as follows (ties between architectures broken towards the integral one, footnote 13).
--
--   1. **$\gamma\le1$.**
--      * If $c<C_M$: $\Pi^*_{LM}>\Pi^*_{SM}$, $\Pi^*_{LM}>\Pi^*_{LI}$, $\Pi^*_{LM}>\Pi^*_{SI}$ — lease modular.
--      * If $C_M\le c<C_{SM}$: $\Pi^*_{SM}\ge\Pi^*_{LM}$, $\Pi^*_{SM}>\Pi^*_{LI}$, $\Pi^*_{SM}>\Pi^*_{SI}$ — sell modular.
--      * If $c\ge C_{SM}$: $\Pi^*_{SI}=\Pi^*_{SM}$, $\Pi^*_{SI}\ge\Pi^*_{LM}$, $\Pi^*_{SI}\ge\Pi^*_{LI}$ — sell integral.
--   2. **$\gamma<1$** (strict version). If $C_M<c<C_{SM}$ then $\Pi^*_{SM}>\Pi^*_{LM}$; if $c\ge C_{SM}$ then $\Pi^*_{SI}>\Pi^*_{LM}$ and $\Pi^*_{SI}>\Pi^*_{LI}$.
--   3. **$\gamma>1$.**
--      * If $c<C_{LM2}$: $\Pi^*_{LM}$ strictly exceeds the other three — lease modular.
--      * If $c\ge C_{LM2}$: $\Pi^*_{LI}=\Pi^*_{LM}$, $\Pi^*_{LI}>\Pi^*_{SM}$, $\Pi^*_{LI}>\Pi^*_{SI}$ — lease integral.
--
--   Here
--   $$C_{SM}=\frac{(1-\delta_2)(\delta_1+\delta_2)}{3\delta_1+5\delta_2},\qquad C_{LM2}=\frac{(1-\gamma\delta_2)(\delta_1+\delta_2)}{3\delta_1+5\delta_2},$$
--   and $C_M$ is the closed form of p. 36 (see the Setting definition).
--
--   The result says when combining leasing with a modular architecture — the configuration promoted by the circular-economy movement — is strictly the most profitable option: only at low production cost, with a cutoff that depends on how well off-lease products are returned.
--
--   **Formalization Note.** The optimal profits are the attained maxima of the four §4 problems, not their closed forms, and the thresholds are the printed closed forms, so neither the profit comparison nor the thresholds hold by definition. $C_{LM2}$ is the corrected threshold. "Prefers" means a strictly larger optimal profit, except where the model has exact ties: $\Pi^*_{SM}=\Pi^*_{SI}$ for $c\ge C_{SM}$ and $\Pi^*_{LM}=\Pi^*_{LI}$ for $\gamma>1$, $c\ge C_{LM2}$ (both resolved towards integral by footnote 13), and, at $\gamma=1$, $\Pi^*_{LM}=\Pi^*_{SM}$ on $[C_M,C_{SM})$ and all four profits equal for $c\ge C_{SM}$. Those comparisons are stated as equalities or weak inequalities for $\gamma\le1$, and the strict versions are restored for $\gamma<1$. The paper's middle range "$C_M\le c\le C_{SM}$" is taken as $[C_M,C_{SM})$, since at $c=C_{SM}$ the tie goes to the integral product. $0<c$ is part of the standing assumptions.
-- source:
--   Agrawal, Atasu & Ülkü, Leasing, Modularity, and the Circular Economy, author manuscript (Management Science, doi:10.1287/mnsc.2020.3829), Proposition 3, p. 17 (proof: Appendix pp. 36–37); footnote 13, p. 12

import Mathlib
import Definitions.Def_LeaseModular_JointChoice_Setting

namespace LeaseModular.JointChoice

/-- Proposition 3, p. 17: the firm's joint choice of business model and architecture. The four
optimal profits `Π*_LM, Π*_SM, Π*_LI, Π*_SI` exist (as attained maxima of the §4 problems), and,
with `C_LM2` corrected and ties broken towards the integral architecture (footnote 13):
* `γ ≤ 1`: for `c < C_M` leasing modular is strictly best; for `C_M ≤ c < C_SM` selling modular is
  strictly better than both integral options and weakly better than leasing modular; for
  `C_SM ≤ c` selling integral ties selling modular and weakly beats both leasing options;
* `γ < 1`: the weak comparisons above are strict (`C_M < c < C_SM`, resp. `C_SM ≤ c`);
* `γ > 1`: for `c < C_LM2` leasing modular is strictly best; for `C_LM2 ≤ c` leasing integral ties
  leasing modular and strictly beats both selling options. -/
theorem proposition_3 (P : Params) (hP : Standing P) :
    ∃ vLM vSM vLI vSI : ℝ,
      IsOptLM P vLM ∧ IsOptSM P vSM ∧ IsOptLI P vLI ∧ IsOptSI P vSI ∧
      (P.γ ≤ 1 →
        (P.c < CM P.δ₁ P.δ₂ P.γ → vSM < vLM ∧ vLI < vLM ∧ vSI < vLM) ∧
        (CM P.δ₁ P.δ₂ P.γ ≤ P.c → P.c < CSM P.δ₁ P.δ₂ →
          vLM ≤ vSM ∧ vLI < vSM ∧ vSI < vSM) ∧
        (CSM P.δ₁ P.δ₂ ≤ P.c → vSM = vSI ∧ vLM ≤ vSI ∧ vLI ≤ vSI)) ∧
      (P.γ < 1 →
        (CM P.δ₁ P.δ₂ P.γ < P.c → P.c < CSM P.δ₁ P.δ₂ → vLM < vSM) ∧
        (CSM P.δ₁ P.δ₂ ≤ P.c → vLM < vSI ∧ vLI < vSI)) ∧
      (1 < P.γ →
        (P.c < CLM2 P.δ₁ P.δ₂ P.γ → vSM < vLM ∧ vLI < vLM ∧ vSI < vLM) ∧
        (CLM2 P.δ₁ P.δ₂ P.γ ≤ P.c → vLM = vLI ∧ vSM < vLI ∧ vSI < vLI)) := by sorry

end LeaseModular.JointChoice
