-- Prove2me | Theorems.Thm_HarmonicKServer_Competitive_adversary_movement
-- name    : HarmonicKServer.Competitive.adversary_movement
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T12:01:26.035844+00:00
-- url     : https://prove2.me/theorems/8fc40c84-979f-4a8f-81eb-a69560a508b3
-- title:
--   Property 2.1 — Adversary movement for the constructed potential
-- statement:
--   Let $k\ge2$ and $X$ be any online configuration, with collocations allowed. If one adversary label moves distance $\delta$ from a distinct-location configuration $Y$ to a distinct-location configuration $Y'$, then the specific Section 4 assignment potential satisfies
--   $$\Phi(X,Y')-\Phi(X,Y)\le2k^4\delta.$$
--   This is the Section 5 verification of Property 2.1 at $\rho=2k^4$, using the concrete $\Phi$, rather than an assumption about an arbitrary potential. Both the corrected energy and the assignment distance carry their exact source coefficients.
--
--   Differences from the source:
--   - encoding: labels [k] with k at least two in Sections 2–5 → Fin k and an explicit 2 ≤ k hypothesis; reason: the finite label change is a bijection; this is the source analysis regime, not a restriction on the headline goal
--   - encoding: an adversary move from Y to Y prime with the distinct-location convention → Y prime is Function.update Y i v and both configurations are injective; reason: this specifies one labelled move without restricting its distance, including zero
--   - encoding: general Property 2.1 with potential Φ and parameter rho → the Section 5 instance with the concrete Section 4 potential and rho = 2k^4; reason: this is the property proved for Harmonic in the headline proof; the general criterion remains a separate item
-- source:
--   Yichen Huang, STOC 2027 submission #95 (October 2026), p. 3, Property 2.1, specialized and proved in §5, p. 10 (PDF p. 11) (PDF p. 4); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/95.pdf; pinned PDF SHA256 20635ef9c29593d01fa406f1a63fdc6b98250e5fc1b1b5c4ed088b407a4e8fd6. Title-page date: November 3, 2026; canonical metadata citation: October 2026.

import Definitions.Def_HarmonicKServer_Competitive_Electrical
import Definitions.Def_HarmonicKServer_Competitive_Harmonic
import Definitions.Def_HarmonicKServer_Competitive_Framework

namespace HarmonicKServer.Competitive
open scoped BigOperators ENNReal
open MeasureTheory

/-- Property 2.1 specialized to Section 4's potential, proved in Section 5. -/
theorem adversary_movement {k : ℕ} (hk : 2 ≤ k) {V : Type*} [MetricSpace V] :
    AdversaryMovement (potential (k := k) (V := V)) (2 * (k : ℝ)^4) := by sorry

end HarmonicKServer.Competitive
