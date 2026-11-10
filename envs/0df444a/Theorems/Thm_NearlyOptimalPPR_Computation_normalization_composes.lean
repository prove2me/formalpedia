-- Prove2me | Theorems.Thm_NearlyOptimalPPR_Computation_normalization_composes
-- name    : NearlyOptimalPPR.Computation.normalization_composes
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T06:37:37.200786+00:00
-- url     : https://prove2.me/theorems/c78117fd-101f-4029-b999-b176eb207b3f
-- title:
--   Lemma 4.3 — Normalization composes across levels
-- statement:
--   Fix an exact-SDDM model, a finite simple unweighted undirected graph with nonisolated seed $s$, real $0<\alpha\le1/2$, $0<\varepsilon\le1$, a depth $\ell$ and a block schedule. Start the operational recursive routine at its prescribed root state, with $q_0=\varepsilon/(32\kappa_0)$ and $\kappa_j=\ell-j+3$. At every normal return at level $j$, necessarily $0\le j\le\ell$, and all return conditions hold:
--
--   $$0\le r_v^{(j)}\le\kappa_jq_jd_v\quad(v\in H_j),$$
--
--   $$0\le r_v^{(t)}\le q_td_v\quad(v\in H_{t-1}\setminus H_t,\ 0\le t\le j),$$
--
--   $$0\le y_v^{(j)}\le3q_j/8\quad(v\in H_{j-1}\setminus H_j),\qquad y_v^{(j)}\ge3q_j/8\quad(v\in H_j).$$
--
--   Here $H_{-1}=V$, references are fixed during each call, and $y^{(0)}=x$. A normal return is the corresponding operational program counter; an ancestor interruption is a different return and makes no accuracy assertion.
--
--   This statement includes the earlier inactive layers, not just the current child layer, so it provides the full interface needed by the parent computation and the pruned root output.
--
--   Differences from the source:
--   - encoding: every normal return of Normalize → every reachable state at the normal-return program counter of the active call; reason: reachability supplies the source algorithm context without assuming the desired return conditions
-- source:
--   Rong-Hua Li, Quanqing Xu, Yichun Yang, Junjie Zhou, STOC 2027 submission #884 (October 2026), Lemma 4.3 p.18; Conditions 4.1–4.2 p.17

import Mathlib
import Definitions.Def_NearlyOptimalPPR_Computation_recursive

set_option autoImplicit false

open Finset Matrix

namespace NearlyOptimalPPR.Computation

/-- Li, Xu, Yang, Zhou, STOC 2027 submission #884 (October 2026),
Lemma 4.3 p.18, Conditions 4.1--4.2 p.17, Algorithms 6--9 pp.20--22.
Only operationally normal returns satisfy the return conditions. -/
theorem normalization_composes (m : SolveModel) (n : ℕ) (g : InputGraph n)
    (s : Fin n) (α ε : ℝ) (ℓ : ℕ) (schedule : BlockSchedule)
    (hα : 0 < α ∧ α ≤ 1 / 2) (hε : 0 < ε ∧ ε ≤ 1)
    (hs : 0 < g.graph.degree s) (t : ℕ) :
    let st := recursiveRun m g s α (rootThreshold ε ℓ) ℓ schedule t
    (st.frames st.top).pc = .normal →
      st.top ≤ ℓ ∧ returnConditions g ℓ st.top st := by sorry

end NearlyOptimalPPR.Computation
