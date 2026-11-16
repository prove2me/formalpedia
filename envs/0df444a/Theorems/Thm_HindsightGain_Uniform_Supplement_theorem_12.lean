-- Prove2me | Theorems.Thm_HindsightGain_Uniform_Supplement_theorem_12
-- name    : HindsightGain.Uniform.Supplement.theorem_12
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T19:05:09.770201+00:00
-- url     : https://prove2.me/theorems/b7e5c898-16e3-4e1b-84fc-c514150a3344
-- title:
--   Theorem 12 — Nonadaptive query lower bound $\Omega(\varepsilon^{-4})$ for $\mathrm{mc}$ and $\beta$
-- statement:
--   There are absolute constants $c,C>0$ such that for every $\varepsilon\in(0,1/64]$ and every $n\ge C\varepsilon^{-2}$ the following holds, for the target $\beta(G)$ and for the target $\mathrm{mc}(G)$. Let $\mathrm{Alg}$ be a randomized nonadaptive algorithm that makes at most $T$ adjacency queries and, for every $n$-vertex graph $G$, outputs with probability at least $2/3$ a number within $\varepsilon n^2$ of the target. Then
--   $$T\ge c\,\varepsilon^{-4}.$$
--
--   This is the nonadaptive half of Theorem 4(b).
--
--   Differences from the source:
--   - encoding: an n-vertex graph → a Mathlib simple graph on Fin n; reason: finite simple graphs up to relabeling
--   - encoding: β(G) (respectively, mc(G)) → a universally quantified target in {mc, β}; reason: the statement holds for each of the two targets
--   - reading: a randomized algorithm → a seed drawn from an arbitrary probability space independent of the input, with output measurable in the seed for every oracle; reason: algorithms driven by random bits have this form; measurability makes the success probability defined
--   - encoding: a nonadaptive algorithm making at most T queries → a seed-determined query set of at most T unordered pairs, the output depending only on the answers to those pairs; reason: this is the source's definition (all queries fixed before any answer)
-- source:
--   Xiaohui Bei, Wenhao Wu, The Optimizer's Windfall: Bounding Hindsight Gain under Random Restrictions, STOC 2027 submission #464 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/464.pdf, Theorem 12, p.33; proof pp.34-35

import Mathlib
import Definitions.Def_HindsightGain_Uniform_Supplement_queries

set_option autoImplicit false
open MeasureTheory

namespace HindsightGain.Uniform.Supplement

/-- Theorem 12, p.33: absolute `c, C > 0`; for `ε ∈ (0, 1/64]`, `n ≥ Cε^{-2}`, either target, and
every randomized nonadaptive algorithm (arbitrary seed space, seed law independent of the input)
that makes at most `T` queries on every seed and is within `εn²` of the target with probability
at least `2/3` on every `n`-vertex graph, `T ≥ cε^{-4}`. -/
theorem theorem_12 :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ (ε : ℝ), 0 < ε → ε ≤ 1 / 64 →
      ∀ (n : ℕ), C * (ε⁻¹) ^ 2 ≤ (n : ℝ) →
      ∀ (tgt : GraphTarget) (Ω : Type) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
        (alg : NonadaptiveAlg n Ω ℝ) (T : ℕ),
        (∀ ω, (alg.queries ω).card ≤ T) →
        (∀ G : SimpleGraph (Fin n),
          (2 : ENNReal) / 3 ≤ μ {ω | |alg.output ω (answers G) - tgt.eval G| ≤ ε * (n : ℝ) ^ 2}) →
        c * (ε⁻¹) ^ 4 ≤ (T : ℝ) := by sorry

end HindsightGain.Uniform.Supplement
