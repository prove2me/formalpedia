-- Prove2me | Theorems.Thm_HGASUndecidable_Main_lemma_4_2
-- name    : HGASUndecidable.Main.lemma_4_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-09T20:14:39.768234+00:00
-- url     : https://prove2.me/theorems/b7742e9c-1c61-4588-90ec-c9ae708a26ac
-- title:
--   Lemma 4.2 — Lyapunov stable iff M*_P < ∞, with the bound ‖y(t)‖_Q ≤ e^{M*_P}‖y(0)‖_Q
-- statement:
--   Use every symmetric positive definite quadratic form Q and every homogeneous polynomial field P of degree D > 1 in dimension n ≥ 1. The angular flow exists, and M*_P is the supremum over all T ≥ 0 of the largest orbit integral of a_P. Lemma 4.2 (Angular criterion for Lyapunov stability [Kor26a, Lemma 2.2]). The origin is Lyapunov stable for ẏ = P(y) if and only if M*_P < ∞. In that case every solution is defined for all t ≥ 0 and satisfies ∥y(t)∥_Q ≤ e^{M*_P}∥y(0)∥_Q.
--
--   Differences from the source:
--   - encoding: Euclidean spaces with coordinates numbered from one → State n = EuclideanSpace ℝ (Fin n), with coordinates numbered from zero; reason: the coordinate identification preserves the Euclidean norm and every instance
--   - encoding: unique maximal solutions, with existence for all forward times included in stability → HasDerivWithinAt on [0,∞), explicit forward existence, and convergence of every forward solution; reason: polynomial fields are locally Lipschitz, so uniqueness and continuation make these formulations equivalent
--   - encoding: the continuous ODE flow on the indicated invariant compact set → existence of a Flow ℝ on that set and the assertion for every Flow whose orbits have the prescribed derivative; reason: the source establishes existence and uniqueness; the relational presentation avoids an opaque ODE-flow constructor and includes existence in the conclusion
--   - encoding: the maximum invariant average and maximum finite-time orbit integral → real suprema over invariant Borel probability measures and initial states, respectively; reason: compactness, continuity and nonemptiness in the source guarantee attainment and boundedness; no maximization is over arbitrary noninvariant measures
--   - encoding: M* belongs to [0,∞] → an EReal supremum over nonnegative times, with toReal used only under M* < ∞; reason: the value at time zero is zero, so the supremum is nonnegative; no unbounded real supremum is silently made finite
-- source:
--   Shevchenko, Liu, Liu (2026), arXiv:2610.12434 (SHA-256 72e185f4750fe9bb72a2f146b2802fa13a97dcdd4f66e0e762b703dc7ddd77a8), Lemma 4.2, printed p. 22 (PDF 24)

import Definitions.Def_HGASUndecidable_Main_Dynamics

open Filter Topology MeasureTheory
open scoped BigOperators

namespace HGASUndecidable.Main

theorem lemma_4_2 {n D : ℕ} (hn : 1 ≤ n) (hD : 1 < D)
    (M : Matrix (Fin n) (Fin n) ℝ) (hM : M.PosDef)
    (P : State n → State n) (hP : PolynomialField P) (hh : Homogeneous D P) :
    (∃ Φ : Flow ℝ (qSphere M), FlowSolves (qSphere M) (angularField M P) Φ) ∧
    ∀ Φ : Flow ℝ (qSphere M), FlowSolves (qSphere M) (angularField M P) Φ →
      (LyapunovStable P ↔ maxIntegralStar Φ (fun y => radialRate M P y.val) < ⊤) ∧
      (LyapunovStable P → ForwardComplete P ∧ ∀ x, ForwardSolution P x →
        ∀ t, 0 ≤ t → qNorm M (x t) ≤
          Real.exp (maxIntegralStar Φ (fun y => radialRate M P y.val)).toReal * qNorm M (x 0)) := by sorry

end HGASUndecidable.Main
