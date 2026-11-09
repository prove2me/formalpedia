-- Prove2me | Theorems.Thm_HarmonicKServer_Competitive_individual_move_bound
-- name    : HarmonicKServer.Competitive.individual_move_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T12:00:07.246091+00:00
-- url     : https://prove2.me/theorems/b2a25f97-c97b-4acb-b121-b139b022a853
-- title:
--   Lemma 4.4 — Individual move bound
-- statement:
--   Let $k\ge2$, let $Y$ be a distinct-location adversary configuration, and let $q$ be a nonnegative integer occupancy of total mass $k$. For labels $i,s$ with $q_i>0$,
--   $$|U_Y(q)-U_Y(q-e_i+e_s)|\le k^3d(y_i,y_s).$$
--   This is a two-sided bound on the change of corrected occupancy energy, including moves with negative energy decrease and the zero move $i=s$. It supplies the magnitude needed for comparing assigned and actual movement distances.
--
--   Differences from the source:
--   - encoding: labels [k] with k at least two in Sections 2–5 → Fin k and an explicit 2 ≤ k hypothesis; reason: the finite label change is a bijection; this is the source analysis regime, not a restriction on the headline goal
--   - encoding: nonnegative integer occupancies q of mass k → natural counts with sum k and guarded natural subtraction; reason: natural numbers represent exactly the nonnegative integers; q_i > 0 makes transfer exact, including i = s
-- source:
--   Yichen Huang, STOC 2027 submission #95 (October 2026), p. 10, Lemma 4.4 (PDF p. 11); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/95.pdf; pinned PDF SHA256 20635ef9c29593d01fa406f1a63fdc6b98250e5fc1b1b5c4ed088b407a4e8fd6. Title-page date: November 3, 2026; canonical metadata citation: October 2026.

import Definitions.Def_HarmonicKServer_Competitive_Electrical
import Definitions.Def_HarmonicKServer_Competitive_Harmonic

namespace HarmonicKServer.Competitive
open scoped BigOperators ENNReal
open MeasureTheory

/-- Lemma 4.4, including i=s and signed potential changes. -/
theorem individual_move_bound {k : ℕ} (hk : 2 ≤ k) {V : Type*} [MetricSpace V]
    (Y : KServer.Config k V) (hY : Function.Injective Y)
    (q : Fin k → ℕ) (hq : Occupancy q) (i s : Fin k) (hi : 0 < q i) :
    |corrected Y q - corrected Y (transfer q i s)| ≤ (k : ℝ)^3 * dist (Y i) (Y s) := by sorry

end HarmonicKServer.Competitive
