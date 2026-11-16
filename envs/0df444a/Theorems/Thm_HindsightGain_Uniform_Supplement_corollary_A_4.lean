-- Prove2me | Theorems.Thm_HindsightGain_Uniform_Supplement_corollary_A_4
-- name    : HindsightGain.Uniform.Supplement.corollary_A_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T18:56:25.830586+00:00
-- url     : https://prove2.me/theorems/fd2a9d44-3d31-49a2-96c7-673ff8782db0
-- title:
--   Corollary A.4 — Every estimator of $\mathrm{mc}$ or $\beta$ examines $\Omega(\varepsilon^{-2})$ vertices
-- statement:
--   There are absolute constants $c,C>0$ such that for every $\varepsilon\in(0,1/64]$ and every $n\ge C\varepsilon^{-2}$ the following holds, for the target $\beta(G)$ and for the target $\mathrm{mc}(G)$. Every randomized algorithm in the adjacency-matrix model, adaptive or not, that on every $n$-vertex graph outputs a number within $\varepsilon n^2$ of the target with probability at least $2/3$ examines at least $c\varepsilon^{-2}$ distinct vertices in the worst case, that is, on some input graph and some outcome of its random seed.
--
--   This is the vertex lower bound of Theorem 4(b).
--
--   Differences from the source:
--   - encoding: an n-vertex graph → a Mathlib simple graph on Fin n; reason: finite simple graphs up to relabeling
--   - encoding: β(G) (respectively, mc(G)) → a universally quantified target in {mc, β}; reason: the statement holds for each of the two targets
--   - reading: a randomized algorithm → a seed drawn from an arbitrary probability space independent of the input, with output measurable in the seed for every oracle; reason: algorithms driven by random bits have this form; measurability makes the success probability defined
--   - encoding: an algorithm, adaptive or not → a seed-selected finite decision tree of pair queries with real outputs; worst case over all seeds and inputs; reason: nonadaptive algorithms are trees whose queries ignore answers; an aborting run may output any number, which only helps the algorithm
-- source:
--   Xiaohui Bei, Wenhao Wu, The Optimizer's Windfall: Bounding Hindsight Gain under Random Restrictions, STOC 2027 submission #464 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/464.pdf, Corollary A.4, p.35

import Mathlib
import Definitions.Def_HindsightGain_Uniform_Supplement_queries

set_option autoImplicit false
open MeasureTheory

namespace HindsightGain.Uniform.Supplement

/-- Corollary A.4, p.35: absolute `c, C > 0`; for `ε ∈ (0, 1/64]`, `n ≥ Cε^{-2}` and either target,
every randomized algorithm, adaptive or not, that is within `εn²` of the target with probability
at least `2/3` on every `n`-vertex graph examines at least `cε^{-2}` distinct vertices on some
input and some seed (worst case). -/
theorem corollary_A_4 :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ (ε : ℝ), 0 < ε → ε ≤ 1 / 64 →
      ∀ (n : ℕ), C * (ε⁻¹) ^ 2 ≤ (n : ℝ) →
      ∀ (tgt : GraphTarget) (Ω : Type) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
        (alg : AdaptiveAlg n Ω),
        (∀ G : SimpleGraph (Fin n),
          (2 : ENNReal) / 3 ≤
            μ {ω | |(alg.tree ω).run (answers G) - tgt.eval G| ≤ ε * (n : ℝ) ^ 2}) →
        ∃ (ω : Ω) (G : SimpleGraph (Fin n)),
          c * (ε⁻¹) ^ 2 ≤ ((examined ((alg.tree ω).queried (answers G))).card : ℝ) := by sorry

end HindsightGain.Uniform.Supplement
