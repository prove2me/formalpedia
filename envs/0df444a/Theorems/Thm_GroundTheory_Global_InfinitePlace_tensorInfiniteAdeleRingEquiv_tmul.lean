-- Prove2me | Theorems.Thm_GroundTheory_Global_InfinitePlace_tensorInfiniteAdeleRingEquiv_tmul
-- name    : GroundTheory.Global.InfinitePlace.tensorInfiniteAdeleRingEquiv_tmul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:56:09.794469+00:00
-- url     : https://prove2.me/theorems/dd26d923-275e-4b70-a499-7984d3cc79b3
-- title:
--   Infinite Place: tensor Infinite Adele Ring Equiv tmul
-- statement:
--   The Infinite Place construction uses the tensor Infinite Adele Ring Equiv tmul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/SemilocalAlgebras/InfiniteAdele.lean#L47-L54
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/SemilocalAlgebras/InfiniteAdele.lean#L47-L54

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_SemilocalAlgebras_Infinite
import Definitions.Def_GroundTheory_GlobalFields_SemilocalAlgebras_InfiniteAdele
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.Global
open NumberField NumberField.InfinitePlace NumberField.InfinitePlace.Completion
open scoped NumberField.LiesOver TensorProduct
open GroundTheory.Global.InfinitePlace
variable {K L : Type*} [Field K] [Field L] [Algebra K L]
variable [NumberField K] [NumberField L]

theorem GroundTheory.Global.InfinitePlace.tensorInfiniteAdeleRingEquiv_tmul (l : L) (x : InfiniteAdeleRing K)
    (w : InfinitePlace L) :
    tensorInfiniteAdeleRingEquiv (l ⊗ₜ x) w =
      (l : w.Completion) * algebraMap (w.comap (algebraMap K L)).Completion w.Completion
        (x (w.comap (algebraMap K L))) := by sorry
