-- Prove2me | Theorems.Thm_OpRiskInspection_Hybrid_ec55_error_correction
-- name    : OpRiskInspection.Hybrid.ec55_error_correction
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T04:35:25.166898+00:00
-- url     : https://prove2.me/theorems/e7c80d71-6fae-4432-8796-ccc09a373e23
-- title:
--   (EC.55), proof of Proposition 5(a)(ii), pp. ec34–ec35 — $V^0_{H(q)}(v)>V^0_R(v)$ iff $v>v^q$, and $v^q<qr$
-- statement:
--   Let $K>0$ and $0<q\le1$, and let $v^q>0$ satisfy (EC.55):
--   $$
--   e^{qr/v^q}=1+\frac{qr}{v^q}+\Big(\frac{qr}{v^q}\Big)^2 .
--   $$
--   Write $V^0_R(v)$ and $V^0_{H(q)}(v)$ for the reduced payoff (6) at frequency $v$ with zero effort, under the random policy and under the hybrid policy $H(q)$ respectively. Then for every $v>0$,
--   $$
--   V^0_{H(q)}(v)>V^0_R(v)\iff v>v^q,
--   $$
--   and moreover $v^q<qr$.
--
--   In error-correction mode (no effort induced), a small periodic component therefore helps at any fixed frequency once $q$ is small enough.
--
--   **Formalization Note** The page writes $V^0(v,P)$, but the zero-effort payoff does not depend on $P$, so $P$ is omitted. The page gives no range for $q$; at $q=0$ both sides coincide and the equivalence fails, so $0<q\le1$ is assumed, matching "$0<q$" in the surrounding proof.
-- source:
--   Kim & Xu, Operational Risk Management: Optimal Inspection Policy, SSRN 3491006 (version of July 2023), pp. ec34–ec35, proof of Proposition 5(a)(ii), (EC.55) and the following sentence

import Mathlib
import Definitions.Def_OpRiskInspection_RandomVsPeriodic_Setting

namespace OpRiskInspection.Hybrid

theorem ec55_error_correction (p : OpRiskInspection.RandomVsPeriodic.Params) (hp : OpRiskInspection.RandomVsPeriodic.Standing p) (K : ℝ) (hK : 0 < K)
    (q : ℝ) (hq0 : 0 < q) (hq1 : q ≤ 1)
    (vq : ℝ) (hvq : 0 < vq)
    (hvqdef : Real.exp (q * p.r / vq) = 1 + q * p.r / vq + (q * p.r / vq) ^ 2) :
    (∀ v : ℝ, 0 < v →
      (OpRiskInspection.RandomVsPeriodic.reducedPayoff p K v (OpRiskInspection.RandomVsPeriodic.randomLaw v) (fun _ => 0) <
          OpRiskInspection.RandomVsPeriodic.reducedPayoff p K v (OpRiskInspection.RandomVsPeriodic.hybridLaw q v) (fun _ => 0) ↔ vq < v)) ∧
    vq < q * p.r := by sorry

end OpRiskInspection.Hybrid
