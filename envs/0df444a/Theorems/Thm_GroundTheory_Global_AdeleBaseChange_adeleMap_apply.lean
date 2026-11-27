-- Prove2me | Theorems.Thm_GroundTheory_Global_AdeleBaseChange_adeleMap_apply
-- name    : GroundTheory.Global.AdeleBaseChange.adeleMap_apply
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T12:54:31.975864+00:00
-- url     : https://prove2.me/theorems/a971bc75-3eb3-5a56-9a3f-56eb77bfc8ca
-- title:
--   Adele Base Change: adele Map apply
-- statement:
--   The Adele Base Change construction uses the adele Map apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/Adele/BaseChange/AdeleEquiv.lean#L22-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/Adele/BaseChange/AdeleEquiv.lean#L22-L25

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_Adele_BaseChange_FiniteTensor
import Definitions.Def_GroundTheory_GlobalFields_SemilocalAlgebras_InfiniteAdeleTopology
import Definitions.Def_GroundTheory_GlobalFields_Adele_BaseChange_AdeleEquiv
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
open IsDedekindDomain NumberField TensorProduct Module Topology
open scoped NumberField.AdeleRing
noncomputable section
open GroundTheory.Global.AdeleBaseChange
variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

theorem GroundTheory.Global.AdeleBaseChange.adeleMap_apply (x : 𝔸[K]) :
    adeleMap K L x =
      (GroundTheory.Global.InfinitePlace.infiniteAdeleRingMap x.1, finiteAdeleMap K L x.2) := by sorry
