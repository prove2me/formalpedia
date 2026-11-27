-- Prove2me | Theorems.Thm_HeteroBass_HetP_Supplement_theorem_7
-- name    : HeteroBass.HetP.Supplement.theorem_7
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-24T00:31:40.331433+00:00
-- url     : https://prove2.me/theorems/0b779fce-4843-44d8-bac4-47296de871de
-- title:
--   Theorem 7 (corrected: coincident neighbor) — adoption from the uniquely determined circle IVP
-- statement:
--   Consider the heterogeneous two-sided Bass circle on any finite $M\ge2$ nodes, with $p_i\ge0$, nonnegative directed neighbor weights, and positive total incoming influence at each node. All consumers are initially nonadopters. There exists a solution $u$ of the full interval system (46), with all initial coordinates one. It is unique on $t\ge0$, agrees on every interval coordinate with the nonadoption observations of the published generator process, and recovers its expected adopter fraction:
--
--   $$f^{2\text{-sided}}_{\mathrm{circle}}(t)=1-\frac1M\sum_{j=1}^M u^j_{0,0}(t),\qquad t\ge0.$$
--
--   The complete system includes every proper anchored interval and the shared all-node coordinate, so the singleton values are determined by a finite linear initial-value problem. The expected fraction on the left remains the published transition-matrix expectation. The statement does not assume the displayed identity or assume a candidate solution already exists. It allows repeated eigenvalues, zero individual edge weights and zero external seeding, subject to (7).
--
--   Differences from the source:
--   - reading: the singleton probabilities can be determined from (46) → existence of a full IVP solution, uniqueness for nonnegative time and equality of every coordinate with the generator observations; reason: Appendix L, (82a)–(82b), pp. 34–35 gives a finite constant-coefficient linear system with fixed initial values; this spells out determination without requiring distinct eigenvalues
--   - correction: the inherited literal M=2 two-boundary notation duplicates the same peer edge → the IVP uses one peer edge at M=2 and the two-boundary formula for M≥3; reason: the explicit identical-network convention on p. 19 and (23), p. 8 fix this boundary; the unit-rate singleton (1+t)e^(−2t) fails a duplicated-edge equation, and no size is excluded
--   - encoding: cyclic intervals and a common full-node nonadoption event for physical time → a finite coordinate family with one full coordinate and equality/uniqueness only on [0,∞); reason: zero-based labels preserve all nodes; values of a proposed solution before time zero are irrelevant; explicit rate hypotheses express (4)–(7)
-- source:
--   Fibich & Golan, Diffusion of new products with heterogeneous consumers, arXiv:2102.05926v3, Theorem 7, (47), p. 19; Lemma 12, (46), pp. 18–19; Appendix L, (82), pp. 34–35

import Mathlib
import Definitions.Def_HeteroBass_HetP_Supplement_IntervalIVP

namespace HeteroBass.HetP.Supplement

theorem theorem_7 {M : ℕ} (hM : 2 ≤ M) (p : Fin M → ℝ)
    (Q : Fin M → Fin M → ℝ) (hp : ∀ i, 0 ≤ p i)
    (hQ : ∀ k j, k ≠ j → 0 ≤ Q k j)
    (hin : ∀ j, 0 < ∑ k ∈ Finset.univ.erase j, Q k j)
    (hcircle : IsTwoSidedCircle Q) :
    ∃ u : ℝ → CircleCoord M → ℝ,
      SolvesCircleIVP p Q u ∧
      (∀ v : ℝ → CircleCoord M → ℝ, SolvesCircleIVP p Q v →
        ∀ t : ℝ, 0 ≤ t → v t = u t) ∧
      (∀ t : ℝ, 0 ≤ t → u t = circleObservation p Q t) ∧
      (∀ t : ℝ, 0 ≤ t → expectedFraction p Q t =
        1 - (1 / (M : ℝ)) * ∑ j : Fin M, u t (intervalCoord j 0 0)) := by sorry

end HeteroBass.HetP.Supplement
