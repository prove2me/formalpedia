-- Prove2me | Theorems.Thm_NearLinearRSP_TwoResources_inner_soundness
-- name    : NearLinearRSP.TwoResources.inner_soundness
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:25:41.159635+00:00
-- url     : https://prove2.me/theorems/dcba182e-2e2d-4b05-9ef2-425cfa73a89d
-- title:
--   Lemma 5.2 — every accepted target has a bicriteria path
-- statement:
--   Fix an inner call with source $s$, thresholds $L,C>0$, accuracy $0<\delta<1$ and its computed DP table. If a target $t\in V$ satisfies $\mathrm{DP}(t,0,0)\le1/4$, then there exists an actual directed $s$–$t$ path $P$ with
--   $$
--   \ell(P)\le(1+\delta)L,\qquad c(P)\le(1+\delta)C.
--   $$
--   This provides the inner bicriteria soundness guarantee. It does not assert an exact feasibility test: an accepted target may have no path with cost at most the unrelaxed budget $C$.
--
--   Differences from the source:
--   - encoding: inner accuracy epsilon and q = Theta(epsilon^-2) → accuracy delta in (0,1), q = ceil(512/delta^2), acceptance 1/4; reason: consistent renaming and an explicit sufficiently large constant, preserving both approximation factors
--   - encoding: the Section 4 DP table on a finite directed graph → the fixed queue computation on incident vertices and the source, with value-one defaults, stable ties and self-loops skipped; reason: isolated vertices cannot be accepted and removing nonnegative self-loops preserves every feasible optimum; no Bellman or correctness property is assumed
-- source:
--   Vikrant Ashvinkumar, STOC 2027 submission #289 (October 2026), p.9, Lemma 5.2

import Definitions.Def_NearLinearRSP_TwoResources_RAM

set_option autoImplicit false

namespace NearLinearRSP.TwoResources

theorem inner_soundness (A : InnerInput) (t : ℕ) (ht : t < A.I.graph.n)
    (haccept : accepted A t) :
    ∃ P : List ℕ, IsPath A.I.graph A.I.source t P ∧
      pathWeight A.I.length P ≤ (1 + A.δ) * A.L ∧
      pathWeight A.I.cost P ≤ (1 + A.δ) * A.I.budget := by sorry

end NearLinearRSP.TwoResources
