-- Prove2me | Theorems.Thm_NonuniformCompetitive_Snoopy_Supplement_theorem_11
-- name    : NonuniformCompetitive.Snoopy.Supplement.theorem_11
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-23T12:08:04.250552+00:00
-- url     : https://prove2.me/theorems/07d7487f-c823-41e0-ac80-2f501e2f5c5a
-- title:
--   Theorem 11 — one deterministic spin learner works for every iid law
-- statement:
--   For every context-switch cost $C>0$ there is a single deterministic measurable history policy $A$, independent of the waiting-time law, such that for every Borel probability law $P$ on $[0,\infty)$,
--   $$\forall c>\frac{e}{e-1}\ \exists a\in\mathbb R\ \forall N\in\mathbb N:\qquad
--   \mathbf E_{P^N} C_A\le c\,\mathbf E_{P^N}\sum_{j=1}^N\min\{\tau_j,C\}+a.$$
--   Each decision uses only the completed waiting times. The same policy works for every strict factor, with a constant depending on $P,C,c$ and not on $N$.
--
--   This is the full distribution-independent existence claim. Atoms at zero, at $C$ or at a selected threshold, arbitrary unbounded support and infinite means are permitted.
--
--   Differences from the source:
--   - encoding: independent nonnegative lock-waiting times from an unknown law → all probability measures on NNReal and every finite iid product horizon; reason: there is no bounded-support, density, continuity or moment assumption
--   - encoding: a deterministic causal learner → a policy chosen before P and c, measurable on every finite history space; reason: expectations over iid inputs are genuine measurable lower integrals
--   - reading: the proof calls the randomized CDF differentiable at all times → no differentiability premise is imposed on the theorem; reason: the theorem concerns arbitrary waiting laws; the proof remark is not a condition of the statement
--   - encoding: the published one-wait cost and offline benchmark → the imported release-at-equality wait cost and min(τ,C) benchmark; reason: this preserves threshold atoms and never converts a nonintegrable expectation to a zero real integral
-- source:
--   Karlin, Manasse, McGeoch, Owicki, Competitive Randomized Algorithms for Nonuniform Problems, Algorithmica 11 (1994), DOI 10.1007/BF01189993, p. 560, Theorem 11 and governing context

import Mathlib
import Definitions.Def_NonuniformCompetitive_Snoopy_Supplement_spinLearning

namespace NonuniformCompetitive.Snoopy.Supplement

open MeasureTheory
open scoped NNReal

/-- Theorem 11, pp.560–561. A single law-independent deterministic measurable
policy works for all iid laws and every strict factor above e/(e-1). No density
hypothesis is imposed; the erroneous differentiability remark in the proof is
not a hypothesis of the theorem. The published release-at-equality convention
is retained, including for atoms at zero, C and the chosen threshold. -/
theorem theorem_11 (C : ℝ) (hC : 0 < C) :
    ∃ A : SpinLearner, ∀ (P : Measure ℝ≥0), IsProbabilityMeasure P →
      ∀ c : ℝ, Real.exp 1 / (Real.exp 1 - 1) < c → SpinIIDCompetitive C A P c := by sorry

end NonuniformCompetitive.Snoopy.Supplement
