-- Prove2me | Theorems.Thm_OnlineSteinitz_Reduction_Supplement_claim_5_6
-- name    : OnlineSteinitz.Reduction.Supplement.claim_5_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T16:21:05.32229+00:00
-- url     : https://prove2.me/theorems/d05150ba-2b60-4e47-8673-1240ec093381
-- title:
--   Claim 5.6 — restricted squared rectangle-discrepancy integral
-- statement:
--   There exists an absolute constant $C>0$ such that for every $N\ge1$, every $N$ points $(u_i,v_i)\in[0,1]^2$, and every positive-measure Lebesgue measurable interval union $E\subseteq[0,1]$, writing $p=|E|$ and $D(x,y)=\#\{i:u_i<x,v_i<y\}-Nxy$, one has
--
--   $$\int_E\int_0^1D(x,y)^2\,dy\,dx\ge Cp^3\log(N+2).$$
--
--   The points may coincide or lie on the boundary. The collection of intervals need not be finite or dyadic. The constant is chosen before $N$, the points and $E$. This is the restricted integral estimate used by Lemma 5.5.
--
--   Differences from the source:
--   - reading: length and integration over a union of intervals → completed-Lebesgue-measurable interval unions; reason: the source uses Lebesgue length and integration; this makes their measurability convention explicit without requiring Borel sets
--   - encoding: the nonnegative squared-discrepancy Lebesgue integral and p=|E| → an iterated nonnegative extended-real integral and p=(volume E).toReal; reason: E is contained in the unit interval and D squared is bounded by N squared, so both are finite and agree with the displayed source quantities
-- source:
--   Russo–Wei, The Online Steinitz Problem, STOC 2027 submission #22 (2026 preprint), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/22.pdf; SHA-256 32ff14f15a94c95630765c77f4fa5a429fb294bcf03a9055ed67c60658769366; Claim 5.6, PDF/printed p.24 (proof continues on the following pages)

import Definitions.Def_OnlineSteinitz_Reduction_Supplement_Rectangles

open MeasureTheory

namespace OnlineSteinitz.Reduction.Supplement

/-- Claim 5.6, pp.24–26. Point multiplicities and all interval unions are retained. -/
theorem claim_5_6 :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 1 ≤ N →
      ∀ pts : Fin N → ℝ × ℝ,
        (∀ i, (pts i).1 ∈ Set.Icc (0 : ℝ) 1 ∧ (pts i).2 ∈ Set.Icc (0 : ℝ) 1) →
      ∀ E : Set ℝ, E ⊆ Set.Icc (0 : ℝ) 1 → IntervalUnion E →
        0 < (volume E).toReal →
        ENNReal.ofReal (C * ((volume E).toReal) ^ 3 * Real.log (N + 2)) ≤
          restrictedEnergy pts E := by sorry

end OnlineSteinitz.Reduction.Supplement
