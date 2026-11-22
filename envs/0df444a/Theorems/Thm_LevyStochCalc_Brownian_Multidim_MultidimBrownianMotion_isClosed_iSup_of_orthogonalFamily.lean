-- Prove2me | Theorems.Thm_LevyStochCalc_Brownian_Multidim_MultidimBrownianMotion_isClosed_iSup_of_orthogonalFamily
-- name    : LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.isClosed_iSup_of_orthogonalFamily
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-20T19:22:26.051964+00:00
-- url     : https://prove2.me/theorems/a9220902-6bc5-4f27-8263-621a5d04b623
-- title:
--   isClosed iSup of orthogonalFamily
-- statement:
--   The source theorem `LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.isClosed_iSup_of_orthogonalFamily` is extracted from `LevyStochCalc.Brownian.PRPMultidimRange`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
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

theorem _root_.LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.isClosed_iSup_of_orthogonalFamily {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E]
    [InnerProductSpace 𝕜 E] {ι : Type*} [Finite ι] {V : ι → Submodule 𝕜 E}
    [∀ i, CompleteSpace (V i)]
    (hV : OrthogonalFamily 𝕜 (fun i => V i) fun i => (V i).subtypeₗᵢ) :
    IsClosed ((⨆ i, V i : Submodule 𝕜 E) : Set E) := by sorry
