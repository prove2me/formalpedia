-- Prove2me | Theorems.Thm_KellyLossNetworks_RevisedDual_Supplement_theorem_6_1
-- name    : KellyLossNetworks.RevisedDual.Supplement.theorem_6_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-24T03:03:35.486294+00:00
-- url     : https://prove2.me/theorems/900bb93a-a406-462f-a284-3323a9fdc169
-- title:
--   Theorem 6.1 — d/dν_r W^π(ν; C) = (1 − L_r^π)(w_r − c_r^π) with c_r^π = W^π(ν; C) − W^π(ν; C − Ae_r)
-- statement:
--   Consider a loss network with fixed routing: incidence matrix $A=(A_{jr})$ with $A_{jr}\in\mathbb Z_+$, rates $\nu_r>0$ and capacities $C\in\mathbb Z_+^J$, with stationary distribution (1.2). A call carried on route $r$ earns $w_r\in\mathbb R$, and the rate of return is $W^\pi(\nu;C)=\mathbb E^\pi\big(\sum_rw_rn_r\big)$. Let $1-L_r^\pi=G(C-Ae_r)/G(C)$ be the stationary acceptance probability of route $r$. Then, for every route $r$,
--   $$\frac{\partial}{\partial\nu_r}W^\pi(\nu;C)=(1-L_r^\pi)\,(w_r-c_r^\pi),\qquad\text{where}\qquad c_r^\pi=W^\pi(\nu;C)-W^\pi(\nu;C-Ae_r).$$
--
--   An additional call offered to route $r$ is accepted with probability $1-L_r^\pi$; if accepted it earns $w_r$ directly but costs $c_r^\pi$ in calls lost later, and $c_r^\pi$ is the shadow price of removing the capacity $Ae_r$ from the network.
--
--   **Formalization Note** The derivative is that of $t\mapsto W^\pi(\nu_1,\dots,\nu_{r-1},t,\nu_{r+1},\dots;C)$ at $t=\nu_r$. If $C-Ae_r$ has a negative entry, $1-L_r^\pi=0$ and the right side vanishes; the value assigned to $W^\pi(\nu;C-Ae_r)$ there is immaterial.
--
--   Differences from the source:
--   - encoding: ν_r rates of the Poisson streams → hypothesis ν_r > 0 for all r; reason: standing positive-rate assumption of the model
--   - encoding: W^π(ν; C − Ae_r) when C − Ae_r has a negative entry (no stationary distribution) → the explicitly defined zero extension; reason: it is multiplied by 1 − L_r^π = 0 in (6.2), so no instance changes
-- source:
--   Kelly, Loss networks, Ann. Appl. Probab. 1(3):319–378 (1991), DOI 10.1214/aoap/1177005872, p. 368, Theorem 6.1, (6.2)–(6.3); W^π in §6.1, p. 368; L_r^π by (1.5), p. 322

import Mathlib
import Definitions.Def_KellyLossNetworks_RevisedDual_Supplement_Exact

namespace KellyLossNetworks.RevisedDual.Supplement

/-- **Theorem 6.1.** `(d/dν_r) W^π(ν; C) = (1 − L_r^π)(w_r − c_r^π)` (6.2), where
`c_r^π = W^π(ν; C) − W^π(ν; C − Ae_r)` (6.3).

Kelly, Loss networks, Ann. Appl. Probab. 1(3):319–378 (1991), DOI 10.1214/aoap/1177005872,
p. 368, Theorem 6.1, (6.2)–(6.3); `W^π` in §6.1, p. 368; `L_r^π` by (1.5), p. 322.

**Formalization Note.** `W^π(ν; C) = revenue A ν (capInt C) w` is the exact expectation of
`Σ_r w_r n_r` under the stationary distribution (1.2); `1 − L_r^π = acceptance`;
`c_r^π = impliedCost`. The derivative is the ordinary derivative of
`t ↦ W^π(ν with ν_r replaced by t; C)` at `t = ν_r`. Rates are positive and the revenues
`w_r` arbitrary reals. When `C − Ae_r` has a negative entry, `1 − L_r^π = 0` and the right side
is `0` whatever value `W^π(ν; C − Ae_r)` is given. -/
theorem theorem_6_1 {J R : ℕ} (A : Fin J → Fin R → ℕ) (ν : Fin R → ℝ)
    (hν : ∀ r, 0 < ν r) (C : Fin J → ℕ) (w : Fin R → ℝ) (r : Fin R) :
    HasDerivAt (fun t : ℝ => revenue A (Function.update ν r t) (capInt C) w)
      (acceptance A ν (capInt C) r * (w r - impliedCost A ν (capInt C) w r)) (ν r) := by sorry

end KellyLossNetworks.RevisedDual.Supplement
