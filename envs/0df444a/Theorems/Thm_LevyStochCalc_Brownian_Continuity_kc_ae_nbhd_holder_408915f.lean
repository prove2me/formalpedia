-- Prove2me | Theorems.Thm_LevyStochCalc_Brownian_Continuity_kc_ae_nbhd_holder_408915f
-- name    : LevyStochCalc.Brownian.Continuity.kc_ae_nbhd_holder_408915f
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-23T13:51:59.506779+00:00
-- url     : https://prove2.me/theorems/995e52e3-0f55-4633-b9ff-6791c33f94da
-- title:
--   Almost-Sure Neighborhood Hölder Bounds
-- statement:
--   This is the almost-sure local Hölder estimate on dyadic rationals. Let $(\Omega,P)$, $X$, $p,q,M$, and `hX` be as above, and assume $\alpha>0$ and $\alpha p<q-1$. Then for $P$-almost every $\omega$ and every $t\in\mathbb R$, there exist $K\ge0$ and $\rho>0$ such that whenever dyadic rationals $s,s'$ lie in $(t-\rho,t+\rho)$,
--
--   $$
--   |X(s,\omega)-X(s',\omega)|\le K|s-s'|^\alpha.
--   $$
--
--   This is the local regularity hypothesis used to extend dyadic paths continuously.
-- source:
--   Lean source: https://github.com/cgarryZA/LevyStochCalc/blob/984dbf0b790031eac05d56fe5a84b65e15e1e932/LevyStochCalc/Brownian/ContinuityKolmogorovBounds.lean#L308-L402 (repository human-ai-mathematics/kls-lean, commit 408915f, module `LevyStochCalc.Brownian.ContinuityKolmogorovBounds`, declaration `LevyStochCalc.Brownian.Continuity.kc_ae_nbhd_holder`; the repository is private at upload time). Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (Apache-2.0; upstream copyright notice retained in the Lean text).

import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_Construction
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_ContinuityDyadicChaining
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.Probability.Distributions.Gaussian.Fernique
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.Kernel.Defs
import Mathlib.Probability.Process.Kolmogorov
import Mathlib.Topology.Order.MonotoneContinuity

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Brownian/ContinuityKolmogorovBounds.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal Topology
section
namespace LevyStochCalc
end LevyStochCalc
open LevyStochCalc
section
namespace LevyStochCalc.Brownian
end LevyStochCalc.Brownian
open LevyStochCalc LevyStochCalc.Brownian
section
namespace LevyStochCalc.Brownian.Continuity
end LevyStochCalc.Brownian.Continuity
open LevyStochCalc LevyStochCalc.Brownian LevyStochCalc.Brownian.Continuity
universe u
variable {Ω : Type u} [MeasurableSpace Ω]

lemma LevyStochCalc.Brownian.Continuity.kc_ae_nbhd_holder_408915f
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℝ → Ω → ℝ) {p q : ℝ} {M : ℝ≥0}
    (hX : ProbabilityTheory.IsKolmogorovProcess X P p q M)
    {α : ℝ} (hα0 : 0 < α) (hαpq : α * p < q - 1) :
    ∀ᵐ ω ∂P, ∀ t : ℝ, ∃ K ρ : ℝ, 0 < ρ ∧ 0 ≤ K ∧ ∀ s ∈ dyadicRationals,
      ∀ s' ∈ dyadicRationals, s ∈ Set.Ioo (t - ρ) (t + ρ) →
        s' ∈ Set.Ioo (t - ρ) (t + ρ) → |X s ω - X s' ω| ≤ K * |s - s'| ^ α := by sorry
