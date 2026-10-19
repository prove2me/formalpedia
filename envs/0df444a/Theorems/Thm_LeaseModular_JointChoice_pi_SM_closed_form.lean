-- Prove2me | Theorems.Thm_LeaseModular_JointChoice_pi_SM_closed_form
-- name    : LeaseModular.JointChoice.pi_SM_closed_form
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-18T22:11:23.411822+00:00
-- url     : https://prove2.me/theorems/67f3ac44-227e-4da0-abec-49f3959e40ef
-- title:
--   Proof of Lemma 1, p. 33 — optimal profit of selling a modular product, with a UN segment iff c < C_SM
-- statement:
--   Throughout, $\delta_1,\delta_2$ are the module durabilities under selling, $\gamma>0$ the relative return condition of off-lease modules (durabilities under leasing $\delta_{kl}=\gamma\delta_k$), and $c$ the per-module production cost, subject to the standing assumptions $0<\delta_2<\delta_1<1$, $\gamma\delta_1<1$, $0<c<(1-\delta_2)/2$ and $c<(1-\gamma\delta_2)/2$.
--
--   When the firm sells a modular product, with $C_{SM}=(1-\delta_2)(\delta_1+\delta_2)/(3\delta_1+5\delta_2)$:
--
--   1. if $c\le C_{SM}$, the optimal profit is
--   $$\Pi^*_{SM}=\frac18\left(\frac{(1-2c-\delta_2)^2}{1-\delta_2}+\frac{(1-2c+2\delta_2+\delta_1)^2}{1+3\delta_1+4\delta_2}\right);$$
--   2. if $c<C_{SM}$, every optimal decision satisfies $S_{n1}<S_{n2}$, i.e. a UN segment is served;
--   3. if $c\ge C_{SM}$, the optimal profit is
--   $$\Pi^*_{SM}=\frac{(2-4c+\delta_1+\delta_2)^2}{8\,(2+3(\delta_1+\delta_2))}.$$
--
--   The two formulas agree at $c=C_{SM}$. The second one equals $\Pi^*_{SI}$: above the threshold modularity is not exercised.
--
--   **Formalization Note.** The SM problem is posed on $0\le S_{n1}\le S_{n2}$, which covers both regimes the paper treats separately on p. 33 (the regime $p_{u2}=0$ and the regime without a UN segment).
-- source:
--   Agrawal, Atasu & Ülkü, Leasing, Modularity, and the Circular Economy, author manuscript (Management Science, doi:10.1287/mnsc.2020.3829), proof of Lemma 1, Appendix p. 33 (Π_SM in the case p*_n1 ≥ P_b1, C_SM, and Π*_SM in the no-UN case)

import Mathlib
import Definitions.Def_LeaseModular_JointChoice_Setting

namespace LeaseModular.JointChoice

/-- Proof of Lemma 1, Appendix p. 33: the optimal SM profit.
* If `c ≤ C_SM(δ₁, δ₂)`, then
  `Π*_SM = (1/8)((1 − 2c − δ₂)²/(1 − δ₂) + (1 − 2c + 2δ₂ + δ₁)²/(1 + 3δ₁ + 4δ₂))`.
* If `c < C_SM(δ₁, δ₂)`, every optimal decision has `S_n1 < S_n2` (a UN segment is served).
* If `C_SM(δ₁, δ₂) ≤ c`, then `Π*_SM = (2 − 4c + δ₁ + δ₂)²/(8(2 + 3(δ₁ + δ₂)))`. -/
theorem pi_SM_closed_form (P : Params) (hP : Standing P) :
    (P.c ≤ CSM P.δ₁ P.δ₂ →
      IsOptSM P ((1 / 8) * ((1 - 2 * P.c - P.δ₂) ^ 2 / (1 - P.δ₂) +
        (1 - 2 * P.c + 2 * P.δ₂ + P.δ₁) ^ 2 / (1 + 3 * P.δ₁ + 4 * P.δ₂)))) ∧
    (P.c < CSM P.δ₁ P.δ₂ → ∀ x, IsMaxSM P x → x.n1 < x.n2) ∧
    (CSM P.δ₁ P.δ₂ ≤ P.c →
      IsOptSM P ((2 - 4 * P.c + P.δ₁ + P.δ₂) ^ 2 / (8 * (2 + 3 * (P.δ₁ + P.δ₂))))) := by sorry

end LeaseModular.JointChoice
