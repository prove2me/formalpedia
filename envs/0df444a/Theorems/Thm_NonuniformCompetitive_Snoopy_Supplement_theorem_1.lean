-- Prove2me | Theorems.Thm_NonuniformCompetitive_Snoopy_Supplement_theorem_1
-- name    : NonuniformCompetitive.Snoopy.Supplement.theorem_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-23T12:00:13.890804+00:00
-- url     : https://prove2.me/theorems/2736cd50-02c0-4ee8-9410-674a34658c05
-- title:
--   Theorem 1 — known-state normalization preserves the factor
-- statement:
--   Let $S$ and $R$ be finite state and request sets of the directed task model, with fixed initial state $s_0$ and canonical state order. Suppose every state admits a finite forcing word that is free there and has positive cost for any schedule avoiding it. If a randomized causal algorithm $A$ is $\alpha$-competitive, then
--   $$\exists A':\quad A'\text{ is }\alpha\text{-competitive},\qquad
--   A'(\sigma)=s\ \text{almost surely whenever opt is known to be in }s.$$
--   The state conclusion is after every nonempty request prefix and includes after-request moves. The factor is preserved exactly, with the source additive-constant convention.
--
--   This removes a state-normalization restriction from competitive analysis; it neither assumes the desired normalization nor assumes its competitive consequence.
--
--   Differences from the source:
--   - encoding: finite states, finite tasks, nonnegative transition and processing costs → finite types, NNReal directed distances, ENNReal processing and work values; reason: infinite processing costs and distinct zero-distance states remain representable
--   - reading: cost comparison and known opt state on processing a request sequence → comparison on finite-offline-cost words and finite known-state work values; reason: all-infinite infeasible words do not define a real offline comparison or a known state
--   - encoding: before, at and after requests, with canonical known-state ties → three causal state maps, a look-ahead-zero equality and a fixed linear order; reason: these retain the move timing and tie convention on p. 545
--   - encoding: a distribution over deterministic algorithms and normalization after each request → measurable fixed-input costs and almost-sure state agreement at every nonempty prefix; reason: the source proof explicitly sums over the algorithm distribution
-- source:
--   Karlin, Manasse, McGeoch, Owicki, Competitive Randomized Algorithms for Nonuniform Problems, Algorithmica 11 (1994), DOI 10.1007/BF01189993, p. 545, Theorem 1 and governing context

import Mathlib
import Definitions.Def_NonuniformCompetitive_Snoopy_Supplement_taskSystem

namespace NonuniformCompetitive.Snoopy.Supplement

open MeasureTheory

/-- Theorem 1, pp.545–546, for the source's directed zero-cost task systems,
with both look-ahead conventions. The canonical order resolves precisely the
known-state ties specified on p.545. Competitiveness concerns feasible finite
inputs; infinite processing costs remain representable in the definitions. -/
theorem theorem_1 {S R : Type} [Fintype S] [Fintype R] [LinearOrder S]
    (T : TaskSystem S R) (s₀ : S) (hw : HasForcingWords T)
    (A : TaskRandomized T) (α : ℝ) (hA : A.Competitive s₀ α) :
    ∃ B : TaskRandomized T, B.Competitive s₀ α ∧
      ∀ (σ : List R) (s : S), σ ≠ [] → TaskKnown T s₀ σ s →
        ∀ᵐ i ∂B.μ, (B.alg i).after σ = s := by sorry

end NonuniformCompetitive.Snoopy.Supplement
