-- Prove2me | Theorems.Thm_LevyStochCalc_Brownian_Continuity_kolmogorov_modification_ae_eq_408915f
-- name    : LevyStochCalc.Brownian.Continuity.kolmogorov_modification_ae_eq_408915f
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-23T13:51:59.557311+00:00
-- url     : https://prove2.me/theorems/215fd72a-e44e-44de-acf7-8239d005c885
-- title:
--   Almost-Sure Equality of a Continuous Modification
-- statement:
--   This is the fixed-time modification-identification lemma. Let $P$ be a probability measure on $\Omega$, let $X:\mathbb R\to\Omega\to\mathbb R$ satisfy `IsKolmogorovProcess X P p q M`, and let $Y:\mathbb R\to\Omega\to\mathbb R$. Assume that $Y(\cdot,\omega)$ is continuous for $P$-almost every $\omega$, and that for every dyadic rational $s$, $Y(s,\omega)=X(s,\omega)$ almost surely. Then for every $t\in\mathbb R$,
--
--   $$
--   Y(t,\omega)=X(t,\omega)\quad\text{for }P\text{-almost every }\omega.
--   $$
--
--   The conclusion is pointwise in the time parameter; it is not a single exceptional null set uniform over all $t$.
-- source:
--   Lean source: https://github.com/cgarryZA/LevyStochCalc/blob/984dbf0b790031eac05d56fe5a84b65e15e1e932/LevyStochCalc/Brownian/ContinuityKolmogorovBounds.lean#L404-L516 (repository human-ai-mathematics/kls-lean, commit 408915f, module `LevyStochCalc.Brownian.ContinuityKolmogorovBounds`, declaration `LevyStochCalc.Brownian.Continuity.kolmogorov_modification_ae_eq`; the repository is private at upload time). Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (Apache-2.0; upstream copyright notice retained in the Lean text).

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

lemma LevyStochCalc.Brownian.Continuity.kolmogorov_modification_ae_eq_408915f
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℝ → Ω → ℝ) {p q : ℝ} {M : ℝ≥0}
    (hX : ProbabilityTheory.IsKolmogorovProcess X P p q M)
    (Y : ℝ → Ω → ℝ)
    (h_continuous : ∀ᵐ ω ∂P, Continuous (fun t => Y t ω))
    (h_dyadic_eq : ∀ s ∈ dyadicRationals, ∀ᵐ ω ∂P, Y s ω = X s ω) :
    ∀ t : ℝ, ∀ᵐ ω ∂P, Y t ω = X t ω := by sorry
