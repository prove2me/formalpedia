-- Prove2me | Theorems.Thm_GroundTheory_Global_ofReal_finsetProd_cpow
-- name    : GroundTheory.Global.ofReal_finsetProd_cpow
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T08:42:44.676736+00:00
-- url     : https://prove2.me/theorems/089fad66-c5c2-4140-b7d5-8b2d97ca7b4a
-- title:
--   Global: of Real finset Prod cpow
-- statement:
--   The Global construction uses the of Real finset Prod cpow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/EulerFactorsInfinite.lean#L27-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/EulerFactorsInfinite.lean#L27-L36

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_EulerFactorsArch
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_GaussianSchwartz
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_TraceFourier
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_HeckeCharRayClass
import Definitions.Def_GroundTheory_GlobalFields_Adele_IntegersLattice
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_EulerFactorsInfinite
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open NumberField InfinitePlace InfinitePlace.Completion MeasureTheory Complex ComplexConjugate
  NumberField.mixedEmbedding Function
open scoped Real SchwartzMap Classical RealInnerProductSpace
open GroundTheory GroundTheory.Global
noncomputable section

theorem GroundTheory.Global.ofReal_finsetProd_cpow {ι : Type*} (t : Finset ι) {r : ι → ℝ} (hr : ∀ i ∈ t, 0 ≤ r i)
    (s : ℂ) : ((∏ i ∈ t, r i : ℝ) : ℂ) ^ s = ∏ i ∈ t, ((r i : ℝ) : ℂ) ^ s := by sorry
