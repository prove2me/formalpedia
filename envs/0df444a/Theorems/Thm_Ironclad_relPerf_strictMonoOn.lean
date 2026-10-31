-- Prove2me | Theorems.Thm_Ironclad_relPerf_strictMonoOn
-- name    : Ironclad.relPerf_strictMonoOn
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T21:26:27.787202+00:00
-- url     : https://prove2.me/theorems/2c8ddb5d-d7e8-4ee0-b9f0-3eb97e9f2ea3
-- title:
--   Appendix .2.6, p.32 — $\mathcal R$ in closed form, strictly increasing in $\theta$
-- statement:
--   Let $0<p_h<1$, $0<q<1$, $\Delta\ge1$, $q_h=(1-q)p_h$, $q_H=qp_h$, let $\alpha(\theta)$ be given by (4) and $\alpha_0=\alpha|_{q=0}$, and let
--
--   $$
--   \mathcal R(\theta)=\frac{\alpha(\theta)/(\theta q+1-q)}{\alpha_0/1}.
--   $$
--
--   Then
--
--   1. $\alpha_0=p_h(1-p_h)^{2\Delta}$;
--   2. for every $\theta$,
--   $$
--   \mathcal R(\theta)=\frac{(1-q_H)^\Delta}{p_h(q_h+\theta q_H)(1-p_h)^{2\Delta}}\Big[q_h^2(1-p_h)^{2\Delta}+q_hq_H(1-p_h)^\Delta(1-q_H)^\Delta+\theta p_hq_H(1-q_H)^\Delta\Big];
--   $$
--   3. $\mathcal R$ is strictly increasing in $\theta$ on $[0,\infty)$.
--
--   Monotonicity reduces Theorem 3.2 to the single value $\theta=1$.
--
--   **Formalization Note** In item 2, at the pole $q_h+\theta q_H=0$ (a negative $\theta$) both sides are $0$ under Lean's $x/0=0$.
--
--   Differences from the source:
--   - generalization: the closed form of $\mathcal R$ (for the paper's $\theta>1$) → for every real $\theta$; reason: specializes to $\theta>1$
--   - generalization: "$\mathcal R$ is increasing in $\theta$" (for $\theta>1$) → on $\theta\ge0$; reason: specializes to $\theta\ge1$
--   - reading: "increasing" → strictly increasing; reason: the chain of strict inequalities on p.33 gives the strict form; it shows $b/d<a/c$, the condition for $f(x)=(ax+b)/(cx+d)$ to increase (the printed "$a/c<b/d$" on p.32 swaps the two sides)
--   - reading: no parameter range in App. .2.6 → $0<p_h<1$, $0<q<1$, $\Delta\ge1$; reason: the proper parameters of Theorem 3.2, whose proof this is
-- source:
--   Zhang, Gong, Li, Wu & Zhang, Improving Blockchain Consistency by Assigning Weights to Random Blocks, arXiv:2107.10467v2, Appendix .2.6, proof of Theorem 3.2, pp.32–33 (R in closed form; "R is increasing in θ"), with α₀ from p.14

import Mathlib
import Definitions.Def_Ironclad_ClosedForms

namespace Ironclad

/-- The ratio `R` in closed form and its monotonicity in `θ`, Zhang, Gong, Li, Wu & Zhang,
*Improving Blockchain Consistency by Assigning Weights to Random Blocks*, arXiv:2107.10467v2, p.14 and Appendix .2.6, pp.32–33. With `α` given by (4):
1. `α₀ = p_h(1 − p_h)^{2Δ}` (equation (4) at `q = 0`, p.14);
2. `R = (1 − q_H)^Δ/(p_h(q_h + θq_H)(1 − p_h)^{2Δ}) · [q_h²(1 − p_h)^{2Δ} + q_h q_H(1 − p_h)^Δ(1 − q_H)^Δ + θp_h q_H(1 − q_H)^Δ]`;
3. `R` is strictly increasing in `θ` on `θ ≥ 0`.

**Formalization Note** Item 2 holds for every real `θ` (at `θq + 1 − q = 0` both sides are `0` in
Lean). The paper says "increasing"; its proof shows the strict form. The standing parameter range
`0 < p_h, q < 1`, `Δ ≥ 1` is that of Theorem 3.2. -/
theorem relPerf_strictMonoOn (ph q : ℝ) (Δ : ℕ) (hph0 : 0 < ph) (hph1 : ph < 1) (hq0 : 0 < q)
    (hq1 : q < 1) (hΔ : 1 ≤ Δ) :
    (∀ θ : ℝ, alphaClosed ph 0 Δ θ = ph * (1 - ph) ^ (2 * Δ)) ∧
    (∀ θ : ℝ, relPerf ph q Δ θ (alphaClosed ph q Δ θ) =
      (1 - qH ph q) ^ Δ / (ph * (qh ph q + θ * qH ph q) * (1 - ph) ^ (2 * Δ)) *
        (qh ph q ^ 2 * (1 - ph) ^ (2 * Δ) + qh ph q * qH ph q * (1 - ph) ^ Δ * (1 - qH ph q) ^ Δ +
          θ * ph * qH ph q * (1 - qH ph q) ^ Δ)) ∧
    StrictMonoOn (fun θ : ℝ => relPerf ph q Δ θ (alphaClosed ph q Δ θ)) (Set.Ici 0) := by sorry

end Ironclad
