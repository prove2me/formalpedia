-- Prove2me | Theorems.Thm_GraphonLabelGame_lemma_4_1
-- name    : GraphonLabelGame.lemma_4_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T04:22:26.571042+00:00
-- url     : https://prove2.me/theorems/9ef5a9d8-f3a2-4b62-bc1f-5d90a6c696ac
-- title:
--   Lemma 4.1 — $\mu\mapsto\langle\mu,h\rangle$ is continuous on $\mathcal P_{\mathrm{Unif}}$ for $h$ continuous only in the state
-- statement:
--   Let $E$ be a Polish space and let $h:[0,1]\times E\to\mathbb R$ be bounded and measurable, with $h(u,\cdot)$ continuous on $E$ for almost every $u\in[0,1]$. Then the map
--   $$\mathcal P_{\mathrm{Unif}}([0,1]\times E)\ni\mu\longmapsto\langle\mu,h\rangle=\int h\,d\mu$$
--   is continuous for the topology of weak convergence.
--
--   Because all measures in $\mathcal P_{\mathrm{Unif}}$ share their first marginal, no continuity in the label variable is needed. The lemma is used to pass from bounded Lipschitz to bounded measurable test functions in the proof of Theorem 6.1.
--
--   Differences from the source:
--   - encoding: h : [0,1] × E → ℝ bounded measurable → h : ℝ × E → ℝ bounded measurable; reason: a function on [0,1] × E extends by 0; measures in P_Unif do not see the extension
--   - encoding: P_Unif([0,1] × E) with the weak topology → the subtype of ProbabilityMeasure (ℝ × E) with first marginal Leb|[0,1], subspace topology; reason: such measures are concentrated on [0,1] × E, and the weak topologies agree
-- source:
--   Lacker, Soret, A Label-State Formulation of Stochastic Graphon Games and Approximate Equilibria on Large Networks, arXiv:2204.09642v1, Lemma 4.1 (= [6, Lemma 2.1]), p.15

import Mathlib
import Definitions.Def_GraphonLabelGame_Kernel

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal

namespace GraphonLabelGame

/-- **Lemma 4.1** ([6, Lemma 2.1]). Lacker–Soret, arXiv:2204.09642v1, Lemma 4.1, p.15.
Let `E` be a Polish space. If `h : [0, 1] × E → ℝ` is bounded and measurable, with `h(u, ·)`
continuous on `E` for a.e. `u ∈ [0, 1]`, then `P_Unif([0, 1] × E) ∋ μ ↦ ⟨μ, h⟩` is continuous.

**Formalization Note** Labels are real numbers and `h` is defined on `ℝ × E`; a function on
`[0, 1] × E` is extended by `0`, which keeps it bounded and measurable, and measures in
`P_Unif` do not see the extension. -/
theorem lemma_4_1 {E : Type*} [TopologicalSpace E] [PolishSpace E] [MeasurableSpace E]
    [BorelSpace E] (h : ℝ × E → ℝ) (hmeas : Measurable h) (hbdd : ∃ C : ℝ, ∀ p, |h p| ≤ C)
    (hcont : ∀ᵐ u ∂lebUnit, Continuous fun x => h (u, x)) :
    Continuous (fun μ : PUnif E => ∫ p, h p ∂(μ.1 : Measure (ℝ × E))) := by sorry

end GraphonLabelGame
