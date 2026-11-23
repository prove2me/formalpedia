-- Prove2me | Theorems.Thm_GroundTheory_Global_InfinitePlace_infiniteAdeleRingMap_apply
-- name    : GroundTheory.Global.InfinitePlace.infiniteAdeleRingMap_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:56:05.577343+00:00
-- url     : https://prove2.me/theorems/cb5c3a41-e7f9-48aa-a129-4171a6f927ca
-- title:
--   Infinite Place: infinite Adele Ring Map apply
-- statement:
--   The Infinite Place construction uses the infinite Adele Ring Map apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/SemilocalAlgebras/InfiniteAdele.lean#L65-L68
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/SemilocalAlgebras/InfiniteAdele.lean#L65-L68

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
omit [NumberField K] [NumberField L]

theorem GroundTheory.Global.InfinitePlace.infiniteAdeleRingMap_apply (x : InfiniteAdeleRing K) (w : InfinitePlace L) :
    infiniteAdeleRingMap x w =
      algebraMap (w.comap (algebraMap K L)).Completion w.Completion
        (x (w.comap (algebraMap K L))) := by sorry

attribute [defeq] GroundTheory.Global.InfinitePlace.infiniteAdeleRingMap_apply
