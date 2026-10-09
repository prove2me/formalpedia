-- Prove2me | Theorems.Thm_OpenPitMIP_Hourglass_pred_complete_of_started
-- name    : OpenPitMIP.Hourglass.pred_complete_of_started
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T10:58:48.135171+00:00
-- url     : https://prove2.me/theorems/0c7cb9c0-c100-4873-8f47-a3dff305b496
-- title:
--   Proof of Theorem 8, p. 1435 — if w_{c̄,t} > 0 then every cluster preceding c̄ is fully extracted by t (PCPSP-F and PCPSP-P)
-- statement:
--   Consider an instance of the PCPSP-C satisfying the standing assumptions, and let $(x,y)$ be feasible for the PCPSP-F (full integrality (10)) or for the PCPSP-P (partial integrality (11)). Write $w_{c,t}=\sum_{t'=1}^{t}x_{c,t'}$. Let $t\in\mathcal T$ and let $c,\bar c$ be clusters with $c\prec\bar c$. If $\bar c$ has started to be extracted by period $t$, then $c$ has been completely extracted by period $t$:
--   $$w_{\bar c,t}>0\ \Longrightarrow\ w_{c,t}=1 .$$
--
--   In the proof of Theorem 8 this is the step "for each $b\in S$, $w_{c(b),t}=1$", since $S$ consists of blocks of strict predecessors of $\bar c$. It fails for the LP relaxation.
--
--   **Formalization Note** The page states the claim for the clusters $c(b)$, $b\in S$; it is stated here for every cluster $c\prec\bar c$, which covers all of them. Feasibility uses the arcs $\mathcal A$ of the transitive reduction only.
-- source:
--   Oper. Res. 68(5), proof of Theorem 8, p. 1435

import Mathlib
import Definitions.Def_OpenPitMIP_Hourglass_Setting

namespace OpenPitMIP.Hourglass

/-- Proof of Theorem 8, p. 1435: "assume `w_{c̄,t} > 0`. Then, for each `b ∈ S`, `w_{c(b),t} = 1`."
Stated per predecessor cluster: at every feasible point of the PCPSP-F or the PCPSP-P, if the
cumulative extraction `w_{c̄,t}` of a cluster `c̄` is positive, then every cluster `c ≺ c̄` is
completely extracted by period `t`, `w_{c,t} = 1`. -/
theorem pred_complete_of_started {B D C : Type} [Fintype B] [Fintype D] [Fintype C] {T m : ℕ}
    (I : PCPSPC B D C T m) (hI : I.Standing) (κ : Integrality)
    (x : C → Fin T → ℝ) (y : B → D → Fin T → ℝ) (hxy : I.Feasible κ x y)
    (t : Fin T) (c cbar : C) (hc : I.cprec c cbar) (hpos : 0 < PCPSPC.cum x cbar t) :
    PCPSPC.cum x c t = 1 := by sorry

end OpenPitMIP.Hourglass
