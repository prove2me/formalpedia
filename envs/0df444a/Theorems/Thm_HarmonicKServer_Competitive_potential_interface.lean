-- Prove2me | Theorems.Thm_HarmonicKServer_Competitive_potential_interface
-- name    : HarmonicKServer.Competitive.potential_interface
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T12:01:15.126057+00:00
-- url     : https://prove2.me/theorems/3d1398f1-4de6-496a-9dd0-c4a9bb35f9f8
-- title:
--   §5, proof of Theorem 1.1 — Attained nonnegative invariant potential
-- statement:
--   For $k\ge2$, every online configuration $X$ and distinct-location adversary configuration $Y$ have an assignment $f$ attaining the Section 4 potential, and
--   $$0\le\Phi(X,Y)=U_Y(q_f)+k^3\sum_\ell d(x_\ell,y_{f(\ell)}).$$
--   For every pair of label permutations $\sigma,\tau$,
--   $$\Phi(X\circ\sigma,Y\circ\tau)=\Phi(X,Y).$$
--   These are the explicit well-posedness assertions used in the proof of Theorem 1.1 on printed page 12. Real-valuedness gives finiteness; the theorem also requires actual attainment, not merely a formal infimum or a chosen assignment.
--
--   Differences from the source:
--   - encoding: labels [k] with k at least two in Sections 2–5 → Fin k and an explicit 2 ≤ k hypothesis; reason: the finite label change is a bijection; this is the source analysis regime, not a restriction on the headline goal
--   - encoding: minimum over the finite collection of assignments → real infimum together with an attaining assignment; reason: the assignment set is finite and nonempty, so this states the source minimum, rather than weakening it
-- source:
--   Yichen Huang, STOC 2027 submission #95 (October 2026), p. 12, §5, proof of Theorem 1.1 (unnumbered supporting assertions) (PDF p. 13); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/95.pdf; pinned PDF SHA256 20635ef9c29593d01fa406f1a63fdc6b98250e5fc1b1b5c4ed088b407a4e8fd6. Title-page date: November 3, 2026; canonical metadata citation: October 2026.

import Definitions.Def_HarmonicKServer_Competitive_Electrical
import Definitions.Def_HarmonicKServer_Competitive_Harmonic
import Definitions.Def_HarmonicKServer_Competitive_Framework

namespace HarmonicKServer.Competitive
open scoped BigOperators ENNReal
open MeasureTheory

/-- The minimum, nonnegativity and relabeling assertions in the proof on printed p. 12. -/
theorem potential_interface {k : ℕ} (hk : 2 ≤ k) {V : Type*} [MetricSpace V] :
    (∀ X Y : KServer.Config k V, Function.Injective Y →
      0 ≤ potential X Y ∧ ∃ f : Fin k → Fin k, assignmentValue X Y f = potential X Y) ∧
    (∀ (X Y : KServer.Config k V) (σ τ : Equiv.Perm (Fin k)), Function.Injective Y →
      potential (X ∘ σ) (Y ∘ τ) = potential X Y) := by sorry

end HarmonicKServer.Competitive
