-- Prove2me | Theorems.Thm_GroundTheory_Global_cycNorm_cycSubOne
-- name    : GroundTheory.Global.cycNorm_cycSubOne
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T06:45:30.311319+00:00
-- url     : https://prove2.me/theorems/837e6bf8-cce9-4309-b7cd-509fec33cfb8
-- title:
--   Global: cyc Norm cyc Sub One
-- statement:
--   The Global construction uses the cyc Norm cyc Sub One property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/HerbrandQuotients/CycTate.lean#L169-L172
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/HerbrandQuotients/CycTate.lean#L169-L172

import Mathlib
import Definitions.Def_GroundTheory_TateCohomology_HerbrandAbstract
import Definitions.Def_GroundTheory_GlobalFields_HerbrandQuotients_CycTate
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
open GroundTheory.GroupCoh
variable {k G V : Type*} [CommRing k] [Group G] [AddCommGroup V] [Module k V]
variable [Fintype G]

theorem GroundTheory.Global.cycNorm_cycSubOne (ρ : Representation k G V) (σ : G) (x : V) :
    cycNorm ρ (cycSubOne ρ σ x) = 0 := by sorry
