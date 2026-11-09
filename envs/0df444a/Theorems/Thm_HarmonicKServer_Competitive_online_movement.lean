-- Prove2me | Theorems.Thm_HarmonicKServer_Competitive_online_movement
-- name    : HarmonicKServer.Competitive.online_movement
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T12:00:39.75943+00:00
-- url     : https://prove2.me/theorems/68b9bcea-6200-4d10-a472-e75e0751a213
-- title:
--   Property 2.2 — Harmonic online movement for the constructed potential
-- statement:
--   Let $k\ge2$ and condition on the completed past, the current request $r$, and the adversary's completed service. Write $X,Y$ for the resulting current configurations, assume $Y$ has distinct locations and covers $r$, and let $X'_i$ be the result of the actual Harmonic label choice $i$, with cost $c_i$. Then
--   $$\sum_i p_i(X,r)\bigl(\Phi(X,Y)-\Phi(X'_i,Y)\bigr)\ge\sum_i p_i(X,r)c_i.$$
--   Thus the conditional expected decrease of the Section 4 potential pays the conditional expected online cost. This includes covered requests, on which the online configuration stays fixed with zero cost. The adversary's completed service is held fixed before this finite average is taken.
--
--   Differences from the source:
--   - encoding: labels [k] with k at least two in Sections 2–5 → Fin k and an explicit 2 ≤ k hypothesis; reason: the finite label change is a bijection; this is the source analysis regime, not a restriction on the headline goal
--   - encoding: conditional expectation in general Property 2.2 → finite label sum for the actual Harmonic kernel and the concrete Section 4 potential; reason: after conditioning on the past and adversary service, these are precisely the possible fresh online outcomes; the arbitrary-seed interaction supplies randomized adaptive policies
-- source:
--   Yichen Huang, STOC 2027 submission #95 (October 2026), p. 3, Property 2.2, specialized and proved in §5, p. 12 (PDF p. 13) (PDF p. 4); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/95.pdf; pinned PDF SHA256 20635ef9c29593d01fa406f1a63fdc6b98250e5fc1b1b5c4ed088b407a4e8fd6. Title-page date: November 3, 2026; canonical metadata citation: October 2026.

import Definitions.Def_HarmonicKServer_Competitive_Electrical
import Definitions.Def_HarmonicKServer_Competitive_Harmonic

namespace HarmonicKServer.Competitive
open scoped BigOperators ENNReal
open MeasureTheory

/-- Property 2.2: the finite conditional law after the request and adversary service. -/
theorem online_movement {k : ℕ} (hk : 2 ≤ k) {V : Type*} [MetricSpace V]
    (X Y : KServer.Config k V) (hY : Function.Injective Y) (r : V) (hr : Covers Y r) :
    (∑ i, harmonicProbability X r i * (potential X Y - potential (harmonicNext X r i) Y)) ≥
      ∑ i, harmonicProbability X r i * harmonicCost X r i := by sorry

end HarmonicKServer.Competitive
