-- Prove2me | Theorems.Thm_FunctionalInequalities_Energy_LipschitzGradient_localSlope_holds_of_relaxation_readable
-- name    : FunctionalInequalities.Energy.LipschitzGradient.localSlope_holds_of_relaxation_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:06:55.741784+00:00
-- url     : https://prove2.me/theorems/b98a1acd-890f-4c84-8b2d-782bb9d924ba
-- title:
--   Relaxed Gradient Constants Imply Local-Slope Constants
-- statement:
--   This theorem transfers a Poincaré constant from the identity-weighted Lipschitz-gradient relaxation to the locally Lipschitz local-slope class.
--
--   Let $V$ be a finite-dimensional complete real inner-product normed space with its Borel measurable structure and second-countable topology. Let $\nu$ be a probability measure on $V$, let $m$ be an additive Haar measure, and assume
--
--   1. $\nu\ll m$;
--   2. $\nu(\partial\operatorname{supp}\nu)=0$;
--   3. for $C\in[0,\infty)$ represented by `NNReal`, the predicate `Poincare.L2Energy.Holds ν (relaxation ν m (ν ≪ m)) C` holds.
--
--   Then
--
--   $$
--   \operatorname{Poincare.LocalSlope.Holds}(\nu,C).
--   $$
--
--   The Lean declaration is `localSlope_holds_of_relaxation_readable`. The statement is an implication between the named formal predicates and does not claim that any Poincaré inequality holds without the stated hypothesis.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.Energy.LipschitzGradient`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem localSlope_holds_of_relaxation (hac : (ν : Measure V) ≪ m)
--       (hfr : (ν : Measure V) (frontier (ν : Measure V).support) = 0) {C : NNReal}
--       (h : Poincare.L2Energy.Holds ν (relaxation ν m hac) C) :
--       Poincare.LocalSlope.Holds ν C
--   ```
--
--   **Module navigation**
--
--   Module: [`Poincare/LipschitzGradient/Comparison`](https://prove2.me/theorems/2c2b9cea-02c3-4658-a545-11edfb033e0d).
--
--   Definition modules: [`Poincare/LocalSlope/Basic`](https://prove2.me/theorems/4e65eb6a-acd3-4142-85a9-b5d14c62f3d1), [`Poincare/L2/Energy`](https://prove2.me/theorems/2c373d63-eba6-4063-92d2-2450951b5927).
--
--   Supporting theorems: [`admissible_iff_memLp_gradient`](https://prove2.me/theorems/284b0183-bfda-452b-b5ff-2efd469c4a7d), [`apply_eq_norm_gradient`](https://prove2.me/theorems/aae816d4-9490-473e-9f62-e3c0294c7ffc).
--
--   Previous: [`holds_ofPreEnergy_of_localSlope`](https://prove2.me/theorems/d102feac-ee7b-49ef-9880-953e2bd04ed9) · Next: [`constant_eq_lipschitz`](https://prove2.me/theorems/ad3e672a-6889-4720-aee1-47c1405b013e).
--
--   [Source excerpt, lines 94–97](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Poincare/LipschitzGradient/Comparison.lean#L94-L97) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Poincare/LipschitzGradient/Comparison.lean#L92-L152 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Poincare.LipschitzGradient.Comparison`, declaration `FunctionalInequalities.Energy.LipschitzGradient.localSlope_holds_of_relaxation`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Poincare_LipschitzGradient_Comparison

open MeasureTheory Filter Topology
universe u
variable {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V]
variable (ν : MeasureTheory.ProbabilityMeasure V) (m : MeasureTheory.Measure V) [m.IsAddHaarMeasure]

theorem FunctionalInequalities.Energy.LipschitzGradient.localSlope_holds_of_relaxation_readable (hac : (ν : Measure V) ≪ m)
    (hfr : (ν : Measure V) (frontier (ν : Measure V).support) = 0) {C : NNReal}
    (h : Poincare.L2Energy.Holds ν (relaxation ν m hac) C) :
    Poincare.LocalSlope.Holds ν C := by sorry
