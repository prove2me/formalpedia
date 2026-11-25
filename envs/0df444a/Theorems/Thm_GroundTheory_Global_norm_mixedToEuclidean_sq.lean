-- Prove2me | Theorems.Thm_GroundTheory_Global_norm_mixedToEuclidean_sq
-- name    : GroundTheory.Global.norm_mixedToEuclidean_sq
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T08:33:50.136441+00:00
-- url     : https://prove2.me/theorems/8e46df16-0590-521c-a622-feeffa988c56
-- title:
--   Global: norm mixed To Euclidean sq
-- statement:
--   The Global construction uses the norm mixed To Euclidean sq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/EulerFactorsInfinite.lean#L40-L54
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/EulerFactorsInfinite.lean#L40-L54

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
variable {K : Type*} [Field K] [NumberField K]

theorem GroundTheory.Global.norm_mixedToEuclidean_sq (x : mixedSpace K) :
    ‖mixedToEuclidean K x‖ ^ 2 = ∑ w, x.1 w ^ 2 + 2 * ∑ w, ‖x.2 w‖ ^ 2 := by sorry
