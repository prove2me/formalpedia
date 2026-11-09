-- Prove2me | Theorems.Thm_HarmonicKServer_Competitive_pairwise_current_bound
-- name    : HarmonicKServer.Competitive.pairwise_current_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T12:00:34.813035+00:00
-- url     : https://prove2.me/theorems/eecff857-cb93-4e84-be36-f925dab73062
-- title:
--   Claim 5.2 — Pairwise current inequality
-- statement:
--   Let $Y$ be a distinct-location adversary configuration with $k\ge2$. Let $q$ be a nonnegative integer occupancy of mass $k$, fix a label $s$, and let $F$ minimize energy for $q+e_s-(1+1/k)\mathbf1$. For all distinct labels $i,j$, each different from $s$,
--   $$F_{ij}(F_{is}-F_{js})\ge-F_{is}F_{js}.$$
--   The standing setup is the one inside Lemma 5.1. The currents are signed electrical currents on the complete metric-resistance network; the conclusion is not asserted of arbitrary antisymmetric matrices.
--
--   Differences from the source:
--   - encoding: labels [k] with k at least two in Sections 2–5 → Fin k and an explicit 2 ≤ k hypothesis; reason: the finite label change is a bijection; this is the source analysis regime, not a restriction on the headline goal
--   - encoding: nonnegative integer occupancies q of mass k → natural counts with sum k, cast to reals in the excess vector; reason: natural numbers represent exactly the nonnegative integers; no natural subtraction occurs in this statement
-- source:
--   Yichen Huang, STOC 2027 submission #95 (October 2026), p. 11, Claim 5.2 within the proof of Lemma 5.1 (PDF p. 12); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/95.pdf; pinned PDF SHA256 20635ef9c29593d01fa406f1a63fdc6b98250e5fc1b1b5c4ed088b407a4e8fd6. Title-page date: November 3, 2026; canonical metadata citation: October 2026.

import Definitions.Def_HarmonicKServer_Competitive_Electrical
import Definitions.Def_HarmonicKServer_Competitive_Harmonic

namespace HarmonicKServer.Competitive
open scoped BigOperators ENNReal
open MeasureTheory

/-- Claim 5.2 with the standing common-flow setup of Lemma 5.1. -/
theorem pairwise_current_bound {k : ℕ} (hk : 2 ≤ k) {V : Type*} [MetricSpace V]
    (Y : KServer.Config k V) (hY : Function.Injective Y)
    (q : Fin k → ℕ) (hq : Occupancy q) (s : Fin k) (F : Flow k)
    (hF : Minimizing Y (commonExcess q s) F)
    (i j : Fin k) (hij : i ≠ j) (his : i ≠ s) (hjs : j ≠ s) :
    F i j * (F i s - F j s) ≥ -F i s * F j s := by sorry

end HarmonicKServer.Competitive
