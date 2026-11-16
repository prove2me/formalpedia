-- Prove2me | Theorems.Thm_HindsightGain_Uniform_Supplement_theorem_4
-- name    : HindsightGain.Uniform.Supplement.theorem_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T18:56:55.9193+00:00
-- url     : https://prove2.me/theorems/2e3f04be-0745-45f9-95fa-a3a09562973f
-- title:
--   Theorem 4 — MaxCut and bipartiteness: $O(\varepsilon^{-2})$ vertices, $\Theta(\varepsilon^{-4})$ nonadaptive queries
-- statement:
--   (a) There is an absolute constant $C>0$ such that for every $\varepsilon\in(0,1)$ and every $n$ there is a randomized nonadaptive algorithm that, given an $n$-vertex graph $G$, examines at most $C\varepsilon^{-2}$ vertices, queries only pairs among them, makes at most $C\varepsilon^{-4}$ queries, and with probability at least $2/3$ outputs estimates of $\mathrm{mc}(G)$ and of $\beta(G)$ that are both within $\pm\varepsilon n^2$.
--
--   (b) There are absolute constants $c,C>0$ such that for every $\varepsilon\in(0,1/64]$, every $n\ge C\varepsilon^{-2}$, and each target $\mathrm{mc}$ or $\beta$:
--   1. every randomized nonadaptive algorithm that estimates the target within $\pm\varepsilon n^2$ with probability at least $2/3$ on every $n$-vertex graph makes at least $c\varepsilon^{-4}$ queries;
--   2. every randomized algorithm with the same guarantee, adaptive or not, examines at least $c\varepsilon^{-2}$ vertices in the worst case.
--
--   Together these determine the vertex-sample and nonadaptive query complexity of estimating the maximum cut and the distance to bipartiteness.
--
--   **Formalization Note** The $O(\cdot)$ bounds of (a) are written with one explicit absolute constant $C$ chosen before $\varepsilon$ and $n$; resources are worst case over all seeds.
--
--   Differences from the source:
--   - encoding: an n-vertex graph → a Mathlib simple graph on Fin n; reason: finite simple graphs up to relabeling
--   - reading: a randomized algorithm → a seed drawn from an arbitrary probability space independent of the input, with output measurable in the seed for every oracle; reason: algorithms driven by random bits have this form; measurability makes the success probability defined
--   - encoding: a nonadaptive algorithm making at most T queries → a seed-determined query set of at most T unordered pairs, the output depending only on the answers to those pairs; reason: this is the source's definition (all queries fixed before any answer)
--   - encoding: an algorithm, adaptive or not → a seed-selected finite decision tree of pair queries with real outputs; worst case over all seeds and inputs; reason: nonadaptive algorithms are trees whose queries ignore answers; an aborting run may output any number, which only helps the algorithm
--   - encoding: β(G) (respectively, mc(G)) → a universally quantified target in {mc, β}; reason: the statement holds for each of the two targets
--   - encoding: examines O(ε^{−2}) randomly chosen vertices and makes O(ε^{−4}) queries → on every seed at most C·ε^{−2} examined vertices and at most C·ε^{−4} queries, with one absolute C before ε and n; reason: O with absolute constants; the examined vertices are by definition the endpoints of the seed-determined queries, so the queries are among them
--   - encoding: with probability at least 2/3 both estimates are accurate → one event of probability at least 2/3 on which both outputs are within εn²; reason: joint accuracy as in the source
-- source:
--   Xiaohui Bei, Wenhao Wu, The Optimizer's Windfall: Bounding Hindsight Gain under Random Restrictions, STOC 2027 submission #464 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/464.pdf, Theorem 4, p.7; (a) by Corollary 5.4 p.26, (b) by Theorem 12 p.33 and Corollary A.4 p.35

import Mathlib
import Definitions.Def_HindsightGain_Uniform_Supplement_queries

set_option autoImplicit false
open MeasureTheory

namespace HindsightGain.Uniform.Supplement

/-- Theorem 4, p.7. (a) One absolute `C`: for every `ε ∈ (0,1)` and `n`, a randomized nonadaptive
algorithm with two outputs that on every seed examines at most `Cε^{-2}` vertices and makes at
most `Cε^{-4}` queries (all among the examined vertices), and on every `n`-vertex graph is within
`εn²` of both `mc(G)` and `β(G)` simultaneously with probability at least `2/3`.
(b) Absolute `c, C > 0`: for `ε ∈ (0, 1/64]`, `n ≥ Cε^{-2}` and either target, every nonadaptive
algorithm with the guarantee makes at least `cε^{-4}` queries, and every algorithm, adaptive or
not, with the guarantee examines at least `cε^{-2}` vertices in the worst case. -/
theorem theorem_4 :
    (∃ C : ℝ, 0 < C ∧ ∀ (ε : ℝ), 0 < ε → ε < 1 → ∀ (n : ℕ),
      ∃ (Ω : Type) (_ : MeasurableSpace Ω) (μ : Measure Ω) (_ : IsProbabilityMeasure μ)
        (alg : NonadaptiveAlg n Ω (ℝ × ℝ)),
        (∀ ω, ((examined (alg.queries ω)).card : ℝ) ≤ C * (ε⁻¹) ^ 2 ∧
          ((alg.queries ω).card : ℝ) ≤ C * (ε⁻¹) ^ 4) ∧
        ∀ G : SimpleGraph (Fin n),
          (2 : ENNReal) / 3 ≤ μ {ω |
            |(alg.output ω (answers G)).1 - (maxCut G : ℝ)| ≤ ε * (n : ℝ) ^ 2 ∧
            |(alg.output ω (answers G)).2 - bipDist G| ≤ ε * (n : ℝ) ^ 2}) ∧
    (∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ (ε : ℝ), 0 < ε → ε ≤ 1 / 64 →
      ∀ (n : ℕ), C * (ε⁻¹) ^ 2 ≤ (n : ℝ) → ∀ (tgt : GraphTarget),
        (∀ (Ω : Type) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
          (alg : NonadaptiveAlg n Ω ℝ) (T : ℕ),
          (∀ ω, (alg.queries ω).card ≤ T) →
          (∀ G : SimpleGraph (Fin n),
            (2 : ENNReal) / 3 ≤ μ {ω | |alg.output ω (answers G) - tgt.eval G| ≤ ε * (n : ℝ) ^ 2}) →
          c * (ε⁻¹) ^ 4 ≤ (T : ℝ)) ∧
        (∀ (Ω : Type) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
          (alg : AdaptiveAlg n Ω),
          (∀ G : SimpleGraph (Fin n),
            (2 : ENNReal) / 3 ≤
              μ {ω | |(alg.tree ω).run (answers G) - tgt.eval G| ≤ ε * (n : ℝ) ^ 2}) →
          ∃ (ω : Ω) (G : SimpleGraph (Fin n)),
            c * (ε⁻¹) ^ 2 ≤ ((examined ((alg.tree ω).queried (answers G))).card : ℝ))) := by sorry

end HindsightGain.Uniform.Supplement
