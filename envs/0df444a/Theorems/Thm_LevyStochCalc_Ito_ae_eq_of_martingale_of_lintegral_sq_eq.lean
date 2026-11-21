-- Prove2me | Theorems.Thm_LevyStochCalc_Ito_ae_eq_of_martingale_of_lintegral_sq_eq
-- name    : LevyStochCalc.Ito.ae_eq_of_martingale_of_lintegral_sq_eq
-- status  : Open
-- author  : @WillR
-- created : 2026-11-20T20:19:08.352162+00:00
-- url     : https://prove2.me/theorems/4065b659-6db9-4e1a-b5d2-c679dd300538
-- title:
--   ae eq of martingale of lintegral sq eq
-- statement:
--   The source theorem `LevyStochCalc.Ito.ae_eq_of_martingale_of_lintegral_sq_eq` is extracted from `LevyStochCalc.BSDEJ.IntegralLocality`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_ItoLocality_F001
import Definitions.Def_LevyStochCalc_Ito_CompensatedLocalityCutoff_F000
import Definitions.Def_LevyStochCalc_Ito_CompensatedLocalityCutoff_F001
import Definitions.Def_LevyStochCalc_Ito_CompensatedLocalityStopping_F000
import Definitions.Def_LevyStochCalc_Ito_CompensatedLocalityStopping_F001
import Definitions.Def_LevyStochCalc_Ito_CompensatedLocalityStopping_F002
import Definitions.Def_LevyStochCalc_Ito_CompensatedLocalityWindow_F000
import Definitions.Def_LevyStochCalc_Ito_CompensatedLocalityWindow_F001
import Definitions.Def_LevyStochCalc_Ito_ItoLevyProcess_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Locality of the canonical stochastic integrals after a horizon

An integrand vanishing after a positive time `c` has an Itô integral that no longer moves after
`c`: the increment of the integral is a martingale increment whose second moment is the energy
carried by `(c, t]`, which is zero. This is the Brownian counterpart of
`LevyStochCalc.Poisson.Compensated.stochasticIntegral_ae_eq_of_vanishing_gt`, together with the
multidimensional version and reformulations for integrands vanishing off a horizon `[0, T]`, the
shape carried by the fields of `LevyStochCalc.BSDEJ.Solves.SolvesBSDEJ`.

## Main statements

* `LevyStochCalc.Ito.ae_eq_of_martingale_of_lintegral_sq_eq` — two times of an `L²` martingale
  with the same second moment carry the same value almost surely.
* `LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian_ae_eq_of_vanishing_gt`
* `LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.stochasticIntegral_ae_eq_of_vanishing_gt`
* `LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian_ae_eq_of_vanish`,
  `LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.stochasticIntegral_ae_eq_of_vanish`,
  `LevyStochCalc.Poisson.Compensated.stochasticIntegral_ae_eq_of_vanish` — the same statements
  for an integrand vanishing off `[0, T]`.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal Topology

universe u v

namespace LevyStochCalc.Ito

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}

theorem _root_.LevyStochCalc.Ito.ae_eq_of_martingale_of_lintegral_sq_eq {M : ℝ → Ω → ℝ} {c t : ℝ} (hct : c ≤ t)
    (hmart : Martingale M ℱ P) (hMt : MemLp (M t) 2 P) (hMc : MemLp (M c) 2 P)
    (hsame : ∫⁻ ω, (‖M t ω‖₊ : ℝ≥0∞) ^ 2 ∂P = ∫⁻ ω, (‖M c ω‖₊ : ℝ≥0∞) ^ 2 ∂P) :
    M t =ᵐ[P] M c := by sorry
