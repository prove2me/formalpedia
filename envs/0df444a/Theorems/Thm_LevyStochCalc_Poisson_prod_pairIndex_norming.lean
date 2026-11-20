-- Prove2me | Theorems.Thm_LevyStochCalc_Poisson_prod_pairIndex_norming
-- name    : LevyStochCalc.Poisson.prod_pairIndex_norming
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T13:09:35.7324+00:00
-- url     : https://prove2.me/theorems/49c66784-95e1-42b4-b59f-f7a36ea56360
-- title:
--   prod pairIndex norming
-- statement:
--   The source theorem `LevyStochCalc.Poisson.prod_pairIndex_norming` is extracted from `LevyStochCalc.Poisson.SecondChaos`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Poisson_SecondChaos_F001

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# The degree-two chaos elements of a finite disjoint family of regions

`pairIndex k l` is the multi-degree carrying one unit at `k` and one at `l`. The chaos element of
that multi-degree is the product `Ñ(B k) Ñ(B l)` of two compensated counts when `k ≠ l`, and
`Ñ(B k) ^ 2 - N(B k)` when `k = l`. For two real profiles `c, c'` constant on each region of the
family, `markedSecondChaos N B c c'` is the quadratic polynomial
`(∑_k c_k Ñ(B k)) (∑_l c'_l Ñ(B l)) - ∑_k c_k c'_k N(B k)` in the counts of the family, and it
expands as the sum of the pair elements weighted by `c_k c'_l`.

On a pairwise disjoint family of regions of finite intensity these elements are centred, and
their Gram is `E[Ψ(c, c') Ψ(e, e')] = ⟨c, e⟩ ⟨c', e'⟩ + ⟨c, e'⟩ ⟨c', e⟩` for the bilinear form
`⟨a, a'⟩ = ∑_k a_k a'_k λ_k` built from the rates `λ_k = ν̂(B k)`; on strips
`B k = (a, b] ×ˢ A k` those rates are `(b - a) ν(A k)`. Both statements come from the
multi-degree orthogonality of `Poisson/SimpleChaos.lean`, the norming `∏_k α_k ! λ_k ^ α_k` at a
pair index, and the fact that two pair indices agree exactly when the pairs agree up to order.

Pairwise disjointness of the family is a hypothesis throughout; overlapping regions are not
covered. The bilinear form is degenerate wherever `λ_k = 0`, and the Gram reads `0 = 0` there.

## Main statements

* `LevyStochCalc.Poisson.pairIndex_eq_iff` — `pairIndex k l = pairIndex k' l'` exactly when
  `(k, l)` and `(k', l')` agree, possibly after a swap.
* `LevyStochCalc.Poisson.poissonChaosProd_pairIndex` — the pair element in closed form,
  `Ñ(B k) Ñ(B l) - δ_(k l) N(B k)`.
* `LevyStochCalc.Poisson.prod_pairIndex_norming` — the norming `∏_k α_k ! λ_k ^ α_k` at a pair
  index is `λ_k λ_l`, doubled on the diagonal.
* `LevyStochCalc.Poisson.integral_poissonChaosProd_pairIndex_mul` — the bilinear moment of two
  pair elements.
* `LevyStochCalc.Poisson.markedSecondChaos_eq_sum` — the quadratic element is the sum of the
  pair elements weighted by `c_k c'_l`.
* `LevyStochCalc.Poisson.integral_markedSecondChaos` — the quadratic elements are centred.
* `LevyStochCalc.Poisson.integral_markedSecondChaos_mul` — the Gram
  `⟨c, e⟩ ⟨c', e'⟩ + ⟨c, e'⟩ ⟨c', e⟩`.
* `LevyStochCalc.Poisson.integral_markedSecondChaos_strip_mul` — the same on strips
  `(a, b] ×ˢ A k` over pairwise disjoint mark sets of finite intensity, at the rates
  `(b - a) ν(A k)`.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace LevyStochCalc.Poisson

universe u v w

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]

/-! ### The multi-degree of a pair of indices -/

theorem _root_.LevyStochCalc.Poisson.prod_pairIndex_norming {p : ℕ} (lam : Fin p → ℝ) (k l : Fin p) :
    (∏ j, ((pairIndex k l j).factorial : ℝ) * lam j ^ (pairIndex k l j))
      = if k = l then 2 * lam k * lam l else lam k * lam l := by sorry
