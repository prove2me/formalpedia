-- Prove2me | Theorems.Thm_HGASUndecidable_Main_lemma_4_1
-- name    : HGASUndecidable.Main.lemma_4_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-09T20:14:28.871743+00:00
-- url     : https://prove2.me/theorems/580022a1-b5f0-476d-9078-25df323d07dc
-- title:
--   Lemma 4.1 — angular criterion: origin GAS iff β(Φ_{Y_P}, a_P) < 0
-- statement:
--   For every dimension n ≥ 1, homogeneous polynomial vector field P of degree D > 1, and symmetric positive definite quadratic form Q(y)=yᵀMy, let S_Q={Q=1}, a_P(y)=yᵀMP(y), and Y_P(y)=P(y)−a_P(y)y. The angular flow on S_Q exists. Lemma 4.1 (Angular criterion for GAS). The origin is GAS for ẏ = P(y) if and only if β(Φ_{Y_P}, a_P) < 0.
--
--   Differences from the source:
--   - encoding: Euclidean spaces with coordinates numbered from one → State n = EuclideanSpace ℝ (Fin n), with coordinates numbered from zero; reason: the coordinate identification preserves the Euclidean norm and every instance
--   - encoding: unique maximal solutions, with existence for all forward times included in stability → HasDerivWithinAt on [0,∞), explicit forward existence, and convergence of every forward solution; reason: polynomial fields are locally Lipschitz, so uniqueness and continuation make these formulations equivalent
--   - encoding: the continuous ODE flow on the indicated invariant compact set → existence of a Flow ℝ on that set and the assertion for every Flow whose orbits have the prescribed derivative; reason: the source establishes existence and uniqueness; the relational presentation avoids an opaque ODE-flow constructor and includes existence in the conclusion
--   - encoding: the maximum invariant average and maximum finite-time orbit integral → real suprema over invariant Borel probability measures and initial states, respectively; reason: compactness, continuity and nonemptiness in the source guarantee attainment and boundedness; no maximization is over arbitrary noninvariant measures
-- source:
--   Shevchenko, Liu, Liu (2026), arXiv:2610.12434 (SHA-256 72e185f4750fe9bb72a2f146b2802fa13a97dcdd4f66e0e762b703dc7ddd77a8), Lemma 4.1, printed p. 21 (PDF 23)

import Definitions.Def_HGASUndecidable_Main_Dynamics

open Filter Topology MeasureTheory
open scoped BigOperators

namespace HGASUndecidable.Main

theorem lemma_4_1 {n D : ℕ} (hn : 1 ≤ n) (hD : 1 < D)
    (M : Matrix (Fin n) (Fin n) ℝ) (hM : M.PosDef)
    (P : State n → State n) (hP : PolynomialField P) (hh : Homogeneous D P) :
    (∃ Φ : Flow ℝ (qSphere M), FlowSolves (qSphere M) (angularField M P) Φ) ∧
    ∀ Φ : Flow ℝ (qSphere M), FlowSolves (qSphere M) (angularField M P) Φ →
      (GAS P ↔ beta Φ (fun y => radialRate M P y.val) < 0) := by sorry

end HGASUndecidable.Main
