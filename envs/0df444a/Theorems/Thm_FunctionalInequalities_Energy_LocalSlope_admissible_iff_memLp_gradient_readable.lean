-- Prove2me | Theorems.Thm_FunctionalInequalities_Energy_LocalSlope_admissible_iff_memLp_gradient_readable
-- name    : FunctionalInequalities.Energy.LocalSlope.admissible_iff_memLp_gradient_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:06:34.197992+00:00
-- url     : https://prove2.me/theorems/284b0183-bfda-452b-b5ff-2efd469c4a7d
-- title:
--   Admissibility Characterized By Function And Gradient $L^2$ Membership
-- statement:
--   This theorem characterizes the existing local-slope admissibility predicate in finite-dimensional Euclidean space.
--
--   Let $E$ be a finite-dimensional complete real inner-product normed space with its Borel measurable structure and second-countable topology. Let $\nu$ be a probability measure on $E$, let $m$ be an additive Haar measure, and assume
--
--   $$
--   \nu\ll m.
--   $$
--
--   For every function $f:E\to\mathbb R$, admissibility with respect to $\nu$ is equivalent to the conjunction of local Lipschitz regularity, square-integrability of $f$, and square-integrability of its gradient:
--
--   $$
--   \operatorname{Admissible}(\nu,f)
--   \iff
--   \operatorname{LocallyLipschitz}(f)\;\land\; f\in L^2(\nu)\;\land\;\nabla f\in L^2(\nu).
--   $$
--
--   The Lean declaration is `admissible_iff_memLp_gradient_readable`. The two $L^2$ conditions are expressed by `MemLp` with exponent $2$; the conclusion is an iff, not merely an implication. The associated gradient energy may take values in $[0,\infty]$, while the displayed $L^2$ membership condition requires finiteness.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.Energy.LocalSlope`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem admissible_iff_memLp_gradient (hν : (ν : Measure E) ≪ m) (f : E → ℝ) :
--       Admissible ν f ↔
--         LocallyLipschitz f ∧ MemLp f 2 (ν : Measure E) ∧ MemLp (gradient f) 2 (ν : Measure E)
--   ```
--
--   **Module navigation**
--
--   Module: [`Energy/LocalSlope/Gradient`](https://prove2.me/theorems/d01ba6e3-090e-46a3-a175-38f38d850838).
--
--   Definition modules: [`Energy/LocalSlope/Basic`](https://prove2.me/theorems/403376af-90fc-4aef-aed0-aefc10593586).
--
--   Supporting theorems: [`apply_eq_norm_gradient`](https://prove2.me/theorems/aae816d4-9490-473e-9f62-e3c0294c7ffc).
--
--   Previous: [`apply_eq_norm_gradient`](https://prove2.me/theorems/aae816d4-9490-473e-9f62-e3c0294c7ffc).
--
--   [Source excerpt, lines 115–117](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Energy/LocalSlope/Gradient.lean#L115-L117) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Energy/LocalSlope/Gradient.lean#L113-L132 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Energy.LocalSlope.Gradient`, declaration `FunctionalInequalities.Energy.LocalSlope.admissible_iff_memLp_gradient`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Energy_LocalSlope_Gradient

open MeasureTheory Filter Topology
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable [MeasurableSpace E] [BorelSpace E] [sct : SecondCountableTopology E]
  [FiniteDimensional ℝ E] (ν : MeasureTheory.ProbabilityMeasure E) (m : MeasureTheory.Measure E)
  [MeasureTheory.Measure.IsAddHaarMeasure m]

theorem FunctionalInequalities.Energy.LocalSlope.admissible_iff_memLp_gradient_readable (hν : (ν : Measure E) ≪ m) (f : E → ℝ) :
    Admissible ν f ↔
      LocallyLipschitz f ∧ MemLp f 2 (ν : Measure E) ∧ MemLp (gradient f) 2 (ν : Measure E) := by sorry
