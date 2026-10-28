-- Prove2me | Theorems.Thm_FunctionalInequalities_Probability_MomentMeasure_exists_convexified_lowerTruncate_variational_le_add_readable
-- name    : FunctionalInequalities.Probability.MomentMeasure.exists_convexified_lowerTruncate_variational_le_add_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:04:48.028919+00:00
-- url     : https://prove2.me/theorems/0380bc20-68ac-4f5a-8497-6a23fbd646e5
-- title:
--   Convexified Competitor Within Epsilon
-- statement:
--   This formalizes the epsilon reduction underlying Proposition 12 of Cordero–Erausquin–Klartag (arXiv:1304.0630v1).
--
--   Let $dx$ be a measure and let $\mu$ be a nonzero finite Borel measure on a real inner-product space. If $f$ is potential-integrable and $\varepsilon>0$, then there exists an integer $n>0$ such that, with
--
--   $$
--   c=\operatorname{Leg}\!\left(\operatorname{Leg}\left(\max(f,-n)\right)\right),
--   $$
--
--   $c$ is a convex lower-semicontinuous potential, is potential-integrable with respect to $\mu$, and
--
--   $$
--   \mathcal V_{dx,\mu}(f)
--   \leq
--   \mathcal V_{dx,\mu}(c)+\varepsilon.
--   $$
--
--   The variational functional and the epsilon are interpreted in `EReal`, so zero and infinite exponential masses remain part of the statement.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.Probability.MomentMeasure`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem exists_convexified_lowerTruncate_variational_le_add [IsFiniteMeasure μ]
--       (dx : Measure E) (f : E → EReal) (hμ : μ ≠ 0) (hf : PotentialIntegrable f μ)
--       (ε : ℝ) (hε : 0 < ε) :
--       ∃ n : ℕ, 0 < n ∧
--         let c := legendre (legendre (lowerTruncate f (n : ℝ)))
--         ConvexPotential c ∧ LowerSemicontinuous c ∧ PotentialIntegrable c μ ∧
--           variationalFunctional dx μ f ≤ variationalFunctional dx μ c + (ε : EReal)
--   ```
--
--   **Module navigation**
--
--   Module: [`Probability/MomentMeasure/Truncation`](https://prove2.me/theorems/38a6a66a-8ebb-44b4-a9b5-ac4aaa092cb2).
--
--   Definition modules: [`Probability/MomentMeasure/Basic`](https://prove2.me/theorems/c1dff218-c76c-41e5-85d4-6f51771cc46c), [`Analysis/Convex/Legendre`](https://prove2.me/theorems/ccf34d51-1332-4642-a3a3-dacdd0cbab81).
--
--   Supporting theorems: [`lowerTruncate_convexification`](https://prove2.me/theorems/1d40fba2-adb7-47d5-9def-9ed116ba3cc6), [`biconjugate_lowerTruncate_potentialIntegrable`](https://prove2.me/theorems/df218836-ab33-4397-add0-3cff5ff33b47).
--
--   [Source excerpt, lines 188–194](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Probability/MomentMeasure/Truncation.lean#L188-L194) · Frozen source `408915f`.
-- source:
--   Source: Cordero-Erausquin–Klartag, Moment measures (arXiv:1304.0630v1), Proposition 12. Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Probability/MomentMeasure/Truncation.lean#L184-L215 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Probability.MomentMeasure.Truncation`, declaration `FunctionalInequalities.Probability.MomentMeasure.exists_convexified_lowerTruncate_variational_le_add`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Probability_MomentMeasure_Truncation

open FunctionalInequalities.Analysis
open MeasureTheory
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] {μ : MeasureTheory.Measure E}

theorem FunctionalInequalities.Probability.MomentMeasure.exists_convexified_lowerTruncate_variational_le_add_readable [IsFiniteMeasure μ]
    (dx : Measure E) (f : E → EReal) (hμ : μ ≠ 0) (hf : PotentialIntegrable f μ)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ n : ℕ, 0 < n ∧
      let c := legendre (legendre (lowerTruncate f (n : ℝ)))
      ConvexPotential c ∧ LowerSemicontinuous c ∧ PotentialIntegrable c μ ∧
        variationalFunctional dx μ f ≤ variationalFunctional dx μ c + (ε : EReal) := by sorry
