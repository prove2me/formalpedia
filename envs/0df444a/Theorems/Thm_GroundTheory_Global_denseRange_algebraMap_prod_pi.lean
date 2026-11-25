-- Prove2me | Theorems.Thm_GroundTheory_Global_denseRange_algebraMap_prod_pi
-- name    : GroundTheory.Global.denseRange_algebraMap_prod_pi
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T16:39:33.66389+00:00
-- url     : https://prove2.me/theorems/94902f33-7346-453a-b9c2-0ffb1cda2e4e
-- title:
--   Global: dense Range algebra Map prod pi
-- statement:
--   The Global construction uses the dense Range algebra Map prod pi property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/Adele/WeakApprox.lean#L74-L106
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/Adele/WeakApprox.lean#L74-L106

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_Adele_WeakApprox
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Global
open IsDedekindDomain NumberField
variable {K : Type*} [Field K] [NumberField K]
variable (S : Finset (HeightOneSpectrum (𝓞 K))) (T : Finset (InfinitePlace K))

theorem GroundTheory.Global.denseRange_algebraMap_prod_pi :
    DenseRange (fun x : K ↦ ((fun v : S ↦ algebraMap K (v.1.adicCompletion K) x),
      (fun w : T ↦ algebraMap K w.1.Completion x))) := by sorry
