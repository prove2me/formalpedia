-- Prove2me | Theorems.Thm_LevyStochCalc_Probability_tendsto_integral_mul_of_tendsto_eLpNorm_real
-- name    : LevyStochCalc.Probability.tendsto_integral_mul_of_tendsto_eLpNorm_real
-- status  : Open
-- author  : @WillR
-- created : 2026-11-20T17:25:33.562494+00:00
-- url     : https://prove2.me/theorems/119f2276-10d6-40b3-aa53-47ea10bcfac4
-- title:
--   tendsto integral mul of tendsto eLpNorm real
-- statement:
--   The source theorem `LevyStochCalc.Probability.tendsto_integral_mul_of_tendsto_eLpNorm_real` is extracted from `LevyStochCalc.Poisson.CompensatedProductMoments`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Poisson_CompensatedProductMoments_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Moments of the compensated product of two bounded mark profiles

For bounded square-integrable mark profiles `f, g : E → ℝ` and the compensated integral `J` over
the step `(a, b]` against a Poisson random measure with intensity `ν`, the compensated product
`Q(f, g) = J(f) J(g) − J(f g) − (b − a) ∫ f g dν` is square integrable and centred, it is
orthogonal in `L²(P)` to `J(h)` for every square-integrable profile `h`, and, with
`⟨u, v⟩ = ∫ u v dν`,

  `E[Q(f, g) Q(f', g')] = (b − a)² (⟨f, f'⟩ ⟨g, g'⟩ + ⟨f, g'⟩ ⟨g, f'⟩)`.

The profiles `f, g` are arbitrary bounded square-integrable functions; their supports may
overlap, and no independence of their compensated integrals enters.

Each of `f, g` is approximated in `L²(ν)` by simple profiles obeying the same bound, and at simple
profiles the identities hold by `Poisson/CompensatedProduct.lean`. The Gram at simple profiles
writes the `L²(P)` distance of two compensated products through `L²(ν)` pairings, so the
compensated products of the approximants form a Cauchy sequence in `L²(P)`. The compensated
integrals of the approximants and of their products converge in `L²(P)` by the isometry
`‖J(f) − J(g)‖_{L²(P)} = √(b − a) ‖f − g‖_{L²(ν)}` at square-integrable profiles; along a
subsequence all of them converge almost surely, which identifies the `L²(P)` limit with
`Q(f, g)`. The identities then pass to the limit by continuity of the `L²` pairing, so no third or
fourth moment of the compensated integral of a general profile is needed.

## Main statements

* `LevyStochCalc.Poisson.integral_compensatedProfile_sub_sq`,
  `LevyStochCalc.Poisson.eLpNorm_compensatedProfile_sub` — the isometry at square-integrable
  profiles.
* `LevyStochCalc.Poisson.memLp_compensatedProduct` — square integrability.
* `LevyStochCalc.Poisson.integral_compensatedProduct` — the mean.
* `LevyStochCalc.Poisson.integral_compensatedProduct_mul` — the Gram.
* `LevyStochCalc.Poisson.integral_compensatedProduct_mul_compensatedProfile` — orthogonality to
  the first chaos.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal Topology

namespace LevyStochCalc.Probability

/-! ### `L²` facts -/

theorem _root_.LevyStochCalc.Probability.tendsto_integral_mul_of_tendsto_eLpNorm_real {α ι : Type*} [MeasurableSpace α]
    {m : Measure α} {l : Filter ι} {X Y : ι → α → ℝ} {X' Y' : α → ℝ} (hX : ∀ i, MemLp (X i) 2 m)
    (hY : ∀ i, MemLp (Y i) 2 m) (hX' : MemLp X' 2 m) (hY' : MemLp Y' 2 m)
    (hXc : Tendsto (fun i => eLpNorm (fun x => X i x - X' x) 2 m) l (𝓝 0))
    (hYc : Tendsto (fun i => eLpNorm (fun x => Y i x - Y' x) 2 m) l (𝓝 0)) :
    Tendsto (fun i => ∫ x, X i x * Y i x ∂m) l (𝓝 (∫ x, X' x * Y' x ∂m)) := by sorry
