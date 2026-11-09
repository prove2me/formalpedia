-- Prove2me | Theorems.Thm_NearLinearRSP_TwoResources_deterministic_retrieval
-- name    : NearLinearRSP.TwoResources.deterministic_retrieval
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:26:49.423263+00:00
-- url     : https://prove2.me/theorems/1abef4e0-8a2f-4e87-a1c3-4447a4c886ad
-- title:
--   Lemma 6.2 — deterministic retrieval succeeds with both resource bounds
-- statement:
--   Fix an inner call with source $s$, thresholds $L,C>0$, accuracy $0<\delta<1$ and its computed table. If $t\in V$ is accepted, namely $\mathrm{DP}(t,0,0)\le1/4$, then the specified deterministic retrieval returns a state whose path $P$ is an actual directed $s$–$t$ path and satisfies
--   $$
--   \ell(P)\le(1+\delta)L,\qquad c(P)\le(1+\delta)C.
--   $$
--   Successful return of the bounded simulation is part of the conclusion, so this states termination as well as both resource guarantees. No returned path, termination invariant, or potential bound is a premise. This supplies the deterministic witnesses promised by the headline theorem.
--
--   Differences from the source:
--   - encoding: inner accuracy epsilon and q = Theta(epsilon^-2) → accuracy delta in (0,1), q = ceil(512/delta^2), acceptance 1/4; reason: consistent renaming and an explicit sufficiently large constant, preserving both approximation factors
--   - encoding: the Section 4 DP table on a finite directed graph → the fixed queue computation on incident vertices and the source, with value-one defaults, stable ties and self-loops skipped; reason: isolated vertices cannot be accepted and removing nonnegative self-loops preserves every feasible optimum; no Bellman or correctness property is assumed
--   - encoding: the deterministic retrieval procedure with counters and multiplicative potential terms → a fixed first-minimum pair rule and a bounded option-valued simulation with fuel (2q+1)(active vertices+1); reason: countdown increases and earlier extraction ranks bound every successful trajectory; failure remains explicit and is not ruled out by definition
-- source:
--   Vikrant Ashvinkumar, STOC 2027 submission #289 (October 2026), p.11, Lemma 6.2; procedure pp.10–11 and termination p.12

import Definitions.Def_NearLinearRSP_TwoResources_RAM

set_option autoImplicit false

namespace NearLinearRSP.TwoResources

theorem deterministic_retrieval (A : InnerInput) (t : ℕ) (ht : t < A.I.graph.n)
    (haccept : accepted A t) :
    ∃ S : RetrievalState, retrieve A t = some S ∧
      IsPath A.I.graph A.I.source t S.path ∧
      pathWeight A.I.length S.path ≤ (1 + A.δ) * A.L ∧
      pathWeight A.I.cost S.path ≤ (1 + A.δ) * A.I.budget := by sorry

end NearLinearRSP.TwoResources
