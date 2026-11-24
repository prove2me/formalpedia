-- Prove2me | Theorems.Thm_GroundTheory_Global_InfinitePlace_piPlacesOverEquiv_apply
-- name    : GroundTheory.Global.InfinitePlace.piPlacesOverEquiv_apply
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T11:27:14.210283+00:00
-- url     : https://prove2.me/theorems/de954886-1f98-4446-8068-86634148afee
-- title:
--   Infinite Place: pi Places Over Equiv apply
-- statement:
--   The Infinite Place construction uses the pi Places Over Equiv apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/SemilocalAlgebras/InfiniteAdele.lean#L34-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/SemilocalAlgebras/InfiniteAdele.lean#L34-L36

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

theorem GroundTheory.Global.InfinitePlace.piPlacesOverEquiv_apply (x : (v : InfinitePlace K) → PiPlacesOver (L := L) v)
    (w : InfinitePlace L) :
    piPlacesOverEquiv x w = x (w.comap (algebraMap K L)) ⟨w, liesOver_comap w⟩ := by sorry

attribute [defeq] GroundTheory.Global.InfinitePlace.piPlacesOverEquiv_apply
