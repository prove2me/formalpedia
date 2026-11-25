-- Prove2me | Theorems.Thm_GroundTheory_Global_AdeleBaseChange_finiteTensorEquiv_tmul
-- name    : GroundTheory.Global.AdeleBaseChange.finiteTensorEquiv_tmul
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T06:34:18.44298+00:00
-- url     : https://prove2.me/theorems/863c6d7d-dd3b-4dd4-998d-8a7aeb5d3ed4
-- title:
--   Adele Base Change: finite Tensor Equiv tmul
-- statement:
--   The Adele Base Change construction uses the finite Tensor Equiv tmul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/Adele/BaseChange/FiniteTensor.lean#L140-L142
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/Adele/BaseChange/FiniteTensor.lean#L140-L142

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_Adele_BaseChange_FiniteCoord
import Definitions.Def_GroundTheory_GlobalFields_Adele_BaseChange_FiniteTensor
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
open IsDedekindDomain NumberField TensorProduct Module Filter Topology
open scoped RestrictedProduct
noncomputable section
open GroundTheory.Global.AdeleBaseChange
open SemiLocal
variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
variable {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Basis ι K L)
attribute [local instance] GroundTheory.Global.AdeleBaseChange._p2m_local_instance_431a99de7f_75
attribute [local instance] GroundTheory.Global.AdeleBaseChange._p2m_local_instance_431a99de7f_78

theorem GroundTheory.Global.AdeleBaseChange.finiteTensorEquiv_tmul (l : L) (a : FiniteAdeleRing (𝓞 K) K) :
    finiteTensorEquiv K L (l ⊗ₜ a) = algebraMap L _ l * finiteAdeleMap K L a := by sorry
