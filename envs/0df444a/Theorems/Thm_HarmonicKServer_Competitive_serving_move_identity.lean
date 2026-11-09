-- Prove2me | Theorems.Thm_HarmonicKServer_Competitive_serving_move_identity
-- name    : HarmonicKServer.Competitive.serving_move_identity
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T12:00:04.724212+00:00
-- url     : https://prove2.me/theorems/8e62a187-fc49-40d7-9514-710d414b8fd8
-- title:
--   Claim 4.2 — Serving move identity
-- statement:
--   Let $Y$ be a distinct-location adversary configuration with $k\ge2$, and let $q$ be a nonnegative integer occupancy of mass $k$. Fix a request label $s$ and a minimizing flow $F$ for $a=q+e_s-(1+1/k)\mathbf1$, with any voltages $h$ satisfying Ohm's law. Every occupied label $i$ satisfies
--   $$U_Y(q)-U_Y(q-e_i+e_s)=k^2(h_i-h_s).$$
--   The identity uses one common electrical field for all serving choices. It includes $i=s$ and imposes no empty-occupancy assumption at $s$.
--
--   Differences from the source:
--   - encoding: labels [k] with k at least two in Sections 2–5 → Fin k and an explicit 2 ≤ k hypothesis; reason: the finite label change is a bijection; this is the source analysis regime, not a restriction on the headline goal
--   - encoding: nonnegative integer occupancies q of mass k → natural counts with sum k and guarded natural subtraction; reason: natural numbers represent exactly the nonnegative integers; q_i > 0 makes transfer exact, including i = s
-- source:
--   Yichen Huang, STOC 2027 submission #95 (October 2026), p. 8, Claim 4.2 (PDF p. 9); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/95.pdf; pinned PDF SHA256 20635ef9c29593d01fa406f1a63fdc6b98250e5fc1b1b5c4ed088b407a4e8fd6. Title-page date: November 3, 2026; canonical metadata citation: October 2026.

import Definitions.Def_HarmonicKServer_Competitive_Electrical
import Definitions.Def_HarmonicKServer_Competitive_Harmonic

namespace HarmonicKServer.Competitive
open scoped BigOperators ENNReal
open MeasureTheory

/-- Claim 4.2; the occupancy at s need not vanish. -/
theorem serving_move_identity {k : ℕ} (hk : 2 ≤ k) {V : Type*} [MetricSpace V]
    (Y : KServer.Config k V) (hY : Function.Injective Y)
    (q : Fin k → ℕ) (hq : Occupancy q) (s : Fin k) (F : Flow k) (h : Vector k)
    (hF : Minimizing Y (commonExcess q s) F) (hh : Ohm Y F h)
    (i : Fin k) (hi : 0 < q i) :
    corrected Y q - corrected Y (transfer q i s) = (k : ℝ)^2 * (h i - h s) := by sorry

end HarmonicKServer.Competitive
