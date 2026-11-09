-- Prove2me | Theorems.Thm_NearLinearRSP_TwoResources_inner_completeness
-- name    : NearLinearRSP.TwoResources.inner_completeness
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:26:08.47159+00:00
-- url     : https://prove2.me/theorems/74151dd7-8061-4a82-b2fe-7d2a57bbefe8
-- title:
--   Lemma 5.1 — every exactly feasible target is accepted
-- statement:
--   Fix an inner call with source $s$, thresholds $L,C>0$, accuracy $0<\delta<1$, and its computed DP table. If a target $t\in V$ admits an $s$–$t$ path $P$ satisfying $\ell(P)\le L$ and $c(P)\le C$, then
--   $$
--   \mathrm{DP}(t,0,0)\le\frac14.
--   $$
--   Thus the inner algorithm accepts every target with an exactly feasible comparator path. The path may revisit edges, and zero resource values are allowed. No correctness condition on the table is supplied as a hypothesis.
--
--   Differences from the source:
--   - encoding: inner accuracy epsilon and q = Theta(epsilon^-2) → accuracy delta in (0,1), q = ceil(512/delta^2), acceptance 1/4; reason: consistent renaming and an explicit sufficiently large constant, preserving both approximation factors
--   - encoding: the Section 4 DP table on a finite directed graph → the fixed queue computation on incident vertices and the source, with value-one defaults, stable ties and self-loops skipped; reason: isolated vertices cannot be accepted and removing nonnegative self-loops preserves every feasible optimum; no Bellman or correctness property is assumed
-- source:
--   Vikrant Ashvinkumar, STOC 2027 submission #289 (October 2026), p.8, Lemma 5.1

import Definitions.Def_NearLinearRSP_TwoResources_RAM

set_option autoImplicit false

namespace NearLinearRSP.TwoResources

theorem inner_completeness (A : InnerInput) (t : ℕ) (ht : t < A.I.graph.n)
    (P : List ℕ) (hP : IsPath A.I.graph A.I.source t P)
    (hL : pathWeight A.I.length P ≤ A.L) (hC : pathWeight A.I.cost P ≤ A.I.budget) :
    accepted A t := by sorry

end NearLinearRSP.TwoResources
