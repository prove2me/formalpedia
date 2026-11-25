-- Prove2me | Theorems.Thm_GroundTheory_Global_AdeleBaseChange_finiteTensorEquiv_symm_apply
-- name    : GroundTheory.Global.AdeleBaseChange.finiteTensorEquiv_symm_apply
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T07:05:00.736343+00:00
-- url     : https://prove2.me/theorems/3455f585-0afe-5c27-b68e-63ad3a3170cb
-- title:
--   Adele Base Change: finite Tensor Equiv symm apply
-- statement:
--   The Adele Base Change construction uses the finite Tensor Equiv symm apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/Adele/BaseChange/FiniteTensor.lean#L144-L147
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/Adele/BaseChange/FiniteTensor.lean#L144-L147

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

theorem GroundTheory.Global.AdeleBaseChange.finiteTensorEquiv_symm_apply (y : FiniteAdeleRing (𝓞 L) L) :
    (finiteTensorEquiv K L).symm y = ∑ i, b i ⊗ₜ finiteCoord b i y := by sorry
