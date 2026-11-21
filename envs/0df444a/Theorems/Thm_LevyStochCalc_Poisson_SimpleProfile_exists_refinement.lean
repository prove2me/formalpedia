-- Prove2me | Theorems.Thm_LevyStochCalc_Poisson_SimpleProfile_exists_refinement
-- name    : LevyStochCalc.Poisson.SimpleProfile.exists_refinement
-- status  : Open
-- author  : @WillR
-- created : 2026-11-20T17:05:59.315305+00:00
-- url     : https://prove2.me/theorems/41d9575a-c4dc-43ea-bf65-09fe172e16b2
-- title:
--   exists refinement
-- statement:
--   The source theorem `LevyStochCalc.Poisson.SimpleProfile.exists_refinement` is extracted from `LevyStochCalc.Poisson.CompensatedProduct`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Poisson_CompensatedProduct_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# The compensated product of two mark profiles over a step

For a mark profile `f : E → ℝ` write `J(f)` for its compensated integral over the step `(a, b]`
against a Poisson random measure `N` with intensity `ν` (`compensatedProfile`). The compensated
product of two mark profiles `f, g` over the step is

  `Q(f, g) = J(f) J(g) − J(f g) − (b − a) ∫ f g dν`.

For bounded square-integrable profiles the product `f g` is again bounded and square integrable,
so each term is a compensated integral of a square-integrable profile.

This file treats simple profiles. The functions of finitely many simple mark profiles are carried
by the mark sets of one simple profile, however the mark sets of different profiles overlap. On
such a common family `A_k`, with coefficient vectors `c, c'`, the compensated product is almost
surely the quadratic element

  `(∑ c_k Ñ(B_k)) (∑ c'_k Ñ(B_k)) − ∑ c_k c'_k N(B_k)`

of the strips `B_k = (a, b] ×ˢ A_k` (`markedSecondChaos`), whose mean, Gram and orthogonality to
the compensated counts come from `Poisson/SecondChaos.lean` and `Poisson/SimpleChaos.lean`. So at
simple profiles `Q` is square integrable and centred, it is orthogonal in `L²(P)` to the
compensated integral of every simple profile, and, with `⟨u, v⟩ = ∫ u v dν`,

  `E[Q(u₁, u₂) Q(u₃, u₄)] = (b − a)² (⟨u₁, u₃⟩ ⟨u₂, u₄⟩ + ⟨u₁, u₄⟩ ⟨u₂, u₃⟩)`.

The profiles need not have disjoint supports, so their compensated integrals need not be
independent. `Poisson/CompensatedProductMoments.lean` extends the identities to bounded
square-integrable profiles.

## Main definitions

* `LevyStochCalc.Poisson.compensatedProduct` — the compensated product of two mark profiles over
  a step.
* `LevyStochCalc.Poisson.SimpleProfile.withCoeff` — the simple profile on the mark sets of a given
  one carrying new coefficients.

## Main statements

* `LevyStochCalc.Poisson.SimpleProfile.exists_refinement` — a common refinement of finitely many
  simple mark profiles.
* `LevyStochCalc.Poisson.SimpleProfile.compensatedProduct_withCoeff_ae_eq` — on a common family
  the compensated product is the quadratic element of the strips.
* `LevyStochCalc.Poisson.SimpleProfile.memLp_compensatedProduct`,
  `LevyStochCalc.Poisson.SimpleProfile.integral_compensatedProduct` — square integrability and the
  mean at simple profiles.
* `LevyStochCalc.Poisson.SimpleProfile.integral_compensatedProduct_mul` — the Gram at simple
  profiles.
* `LevyStochCalc.Poisson.SimpleProfile.integral_compensatedProduct_mul_compensatedProfile` —
  orthogonality to the first chaos at simple profiles.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal

namespace LevyStochCalc.Poisson

universe u v

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]

namespace SimpleProfile

omit [SigmaFinite ν] in

theorem _root_.LevyStochCalc.Poisson.SimpleProfile.exists_refinement {ι : Type*} [Finite ι] (G : ι → SimpleProfile E ν) :
    ∃ (H : SimpleProfile E ν) (d : ι → Fin H.K → ℝ),
      ∀ i e, (H.withCoeff (d i)).toFun e = (G i).toFun e := by sorry
