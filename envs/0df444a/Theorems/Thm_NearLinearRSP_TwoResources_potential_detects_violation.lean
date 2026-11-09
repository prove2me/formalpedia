-- Prove2me | Theorems.Thm_NearLinearRSP_TwoResources_potential_detects_violation
-- name    : NearLinearRSP.TwoResources.potential_detects_violation
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:25:50.032973+00:00
-- url     : https://prove2.me/theorems/5797a052-8474-467f-b721-60758447787a
-- title:
--   Observation 6.1 — both resource violations force potential at least one
-- statement:
--   Fix an inner call with thresholds $L,C>0$ and accuracy $0<\delta<1$. Let the specified deterministic retrieval from a target $t\in V$ output a final state with path $P$, counters $Q_\ell,Q_c$ and final potential $\Phi$. Both implications hold:
--   $$
--   \bigl(\ell(P)>(1+\delta)L\ \land\ Q_\ell<q\bigr)\Longrightarrow\Phi\ge1,
--   $$
--   $$
--   \bigl(c(P)>(1+\delta)C\ \land\ Q_c<q\bigr)\Longrightarrow\Phi\ge1.
--   $$
--   The potential is evaluated at the final front vertex and counters, with its two occurrence-preserving products of strictly positive Poisson generating functions. This detects either resource violation without assuming acceptance or a favorable potential value.
--
--   Differences from the source:
--   - encoding: inner accuracy epsilon and q = Theta(epsilon^-2) → accuracy delta in (0,1), q = ceil(512/delta^2), acceptance 1/4; reason: consistent renaming and an explicit sufficiently large constant, preserving both approximation factors
--   - encoding: the Section 4 DP table on a finite directed graph → the fixed queue computation on incident vertices and the source, with value-one defaults, stable ties and self-loops skipped; reason: isolated vertices cannot be accepted and removing nonnegative self-loops preserves every feasible optimum; no Bellman or correctness property is assumed
--   - encoding: the deterministic retrieval procedure with counters and multiplicative potential terms → a fixed first-minimum pair rule and a bounded option-valued simulation with fuel (2q+1)(active vertices+1); reason: countdown increases and earlier extraction ranks bound every successful trajectory; failure remains explicit and is not ruled out by definition
--   - encoding: expectations of powers of Poisson increments in the potential → the exact generating functions exp(mu*(z-1)) in both positive denominators; reason: these are the same expectations, including value one at rate zero, without a Bochner-integral default
-- source:
--   Vikrant Ashvinkumar, STOC 2027 submission #289 (October 2026), p.11, Observation 6.1

import Definitions.Def_NearLinearRSP_TwoResources_RAM

set_option autoImplicit false

namespace NearLinearRSP.TwoResources

theorem potential_detects_violation (A : InnerInput) (t : ℕ) (ht : t < A.I.graph.n)
    (S : RetrievalState) (houtput : retrieve A t = some S) :
    (pathWeight A.I.length S.path > (1 + A.δ) * A.L → S.i < tickLimit A →
      1 ≤ potential A S) ∧
    (pathWeight A.I.cost S.path > (1 + A.δ) * A.I.budget → S.j < tickLimit A →
      1 ≤ potential A S) := by sorry

end NearLinearRSP.TwoResources
