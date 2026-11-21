-- Prove2me | Theorems.Thm_LevyStochCalc_Brownian_Multidim_MultidimBrownianMotion_orthogonalFamily_itoRange
-- name    : LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.orthogonalFamily_itoRange
-- status  : Open
-- author  : @WillR
-- created : 2026-11-20T19:22:37.468888+00:00
-- url     : https://prove2.me/theorems/792ad24a-5704-414a-9726-e042831b1746
-- title:
--   orthogonalFamily itoRange
-- statement:
--   The source theorem `LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.orthogonalFamily_itoRange` is extracted from `LevyStochCalc.Brownian.PRPMultidimRange`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_CrossOrthogonalityDirectCross_F000
import Definitions.Def_LevyStochCalc_Brownian_CrossOrthogonalityDirectCross_F001
import Definitions.Def_LevyStochCalc_Brownian_CrossOrthogonalityLimit_F000
import Definitions.Def_LevyStochCalc_Brownian_CrossOrthogonalityLimit_F001
import Definitions.Def_LevyStochCalc_Brownian_CrossOrthogonalityLimit_F002
import Definitions.Def_LevyStochCalc_Brownian_ItoRange_F001
import Definitions.Def_LevyStochCalc_Brownian_ItoRange_F002
import Mathlib.MeasureTheory.Measure.NullMeasurable

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# The closed range of the multidimensional Brownian Itô integral

The multidimensional Itô integral is the sum over the coordinates of the scalar integrals, so its
range in `L²` is the supremum of the scalar ranges. Those are closed, and orthogonal to one
another, so the supremum is closed: a point of its closure is the sum of its orthogonal
projections, each of which lies in the corresponding scalar range. The orthogonal decomposition
along the supremum then represents every square-integrable weight of mean zero, measurable before
the horizon, as a sum of coordinate Itô integrals, given the separation hypothesis.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal Topology

namespace LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion

open LevyStochCalc.Brownian.Ito

universe u

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {d : ℕ}

section Range

variable (W : MultidimBrownianMotion P d) {ℱ : Filtration ℝ ‹MeasurableSpace Ω›} {T : ℝ}
  (hcoord : ∀ k : Fin d, IsBrownianFiltration (W.W k) ℱ)

theorem _root_.LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.orthogonalFamily_itoRange (hT : 0 < T) :
    OrthogonalFamily ℝ
      (fun i : Fin d => (itoRange (W.W i) (hcoord i) hT : Submodule ℝ (Lp ℝ 2 P)))
      (fun i => (itoRange (W.W i) (hcoord i) hT).subtypeₗᵢ) := by sorry
