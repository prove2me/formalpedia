-- Prove2me | Theorems.Thm_LeaseModular_JointChoice_lemma_1
-- name    : LeaseModular.JointChoice.lemma_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-18T22:11:26.630019+00:00
-- url     : https://prove2.me/theorems/7a0b6808-61e9-4d17-9948-3ded05016062
-- title:
--   Lemma 1, p. 12 — under selling, modularity is strictly more profitable (and a UN segment exists) iff c < C_SM(δ1,δ2)
-- statement:
--   Throughout, $\delta_1,\delta_2$ are the module durabilities under selling, $\gamma>0$ the relative return condition of off-lease modules (durabilities under leasing $\delta_{kl}=\gamma\delta_k$), and $c$ the per-module production cost, subject to the standing assumptions $0<\delta_2<\delta_1<1$, $\gamma\delta_1<1$, $0<c<(1-\delta_2)/2$ and $c<(1-\gamma\delta_2)/2$.
--
--   Under selling, modularity leads to strictly higher profit if and only if the production cost is below $C_{SM}(\delta_1,\delta_2)=\frac{(1-\delta_2)(\delta_1+\delta_2)}{3\delta_1+5\delta_2}$. Precisely, the optimal profits $\Pi^*_{SM}$ and $\Pi^*_{SI}$ exist and
--   $$\Big(\Pi^*_{SM}>\Pi^*_{SI}\ \text{and every optimal SM decision has } S_{n1}<S_{n2}\Big)\iff c<C_{SM}(\delta_1,\delta_2).$$
--   Moreover:
--
--   1. $c<C_{SM}(\delta_1,\delta_2)$ if and only if $\delta_2<D_S(\delta_1,c)=\tfrac12\big(1-5c-\delta_1+\sqrt{25c^2+(1+\delta_1)^2-2c(5+\delta_1)}\big)$;
--   2. $C_{SM}$ is strictly increasing in $\delta_1$ on $(\delta_2,1)$ and strictly decreasing in $\delta_2$ on $(0,\delta_1)$.
--
--   Modularity pays under selling only when customers replace the less durable module on its own, which happens at low production cost or with a large durability gap between the modules.
--
--   **Formalization Note.** "The UN segment exists" is a property of the optimal decision and is stated for every optimal decision. The monotonicity domains are the standing range of the varied parameter with the others fixed.
-- source:
--   Agrawal, Atasu & Ülkü, Leasing, Modularity, and the Circular Economy, author manuscript (Management Science, doi:10.1287/mnsc.2020.3829), Lemma 1, p. 12 (proof: Appendix pp. 31–33)

import Mathlib
import Definitions.Def_LeaseModular_JointChoice_Setting

namespace LeaseModular.JointChoice

/-- Lemma 1, p. 12. Under selling, modularity gives strictly higher profit and a UN segment exists
(`Π*_SM > Π*_SI`, and every optimal SM decision has `S_n1 < S_n2`) if and only if
`c < C_SM(δ₁, δ₂)`; this condition is equivalent to `δ₂ < D_S(δ₁, c)`; and `C_SM` is strictly
increasing in `δ₁` (on `δ₁ ∈ (δ₂, 1)`) and strictly decreasing in `δ₂` (on `δ₂ ∈ (0, δ₁)`). -/
theorem lemma_1 (P : Params) (hP : Standing P) :
    (∃ vSM vSI : ℝ, IsOptSM P vSM ∧ IsOptSI P vSI ∧
      ((vSI < vSM ∧ ∀ x, IsMaxSM P x → x.n1 < x.n2) ↔ P.c < CSM P.δ₁ P.δ₂)) ∧
    (P.c < CSM P.δ₁ P.δ₂ ↔ P.δ₂ < DS P.δ₁ P.c) ∧
    StrictMonoOn (fun d => CSM d P.δ₂) (Set.Ioo P.δ₂ 1) ∧
    StrictAntiOn (fun d => CSM P.δ₁ d) (Set.Ioo 0 P.δ₁) := by sorry

end LeaseModular.JointChoice
