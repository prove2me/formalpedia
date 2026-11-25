-- Prove2me | Theorems.Thm_GroundTheory_Global_AdeleBaseChange_finiteTensorHomeomorph_apply
-- name    : GroundTheory.Global.AdeleBaseChange.finiteTensorHomeomorph_apply
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T08:25:54.37651+00:00
-- url     : https://prove2.me/theorems/0e83d306-e841-44b3-88f7-2aaa1ff026e8
-- title:
--   Adele Base Change: finite Tensor Homeomorph apply
-- statement:
--   The Adele Base Change construction uses the finite Tensor Homeomorph apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/Adele/BaseChange.lean#L210-L212
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/Adele/BaseChange.lean#L210-L212

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_Adele_BaseChange_AdeleEquiv
import Definitions.Def_GroundTheory_GlobalFields_Adele_BaseChange
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
open scoped NumberField.AdeleRing RestrictedProduct
noncomputable section
open GroundTheory.Global.AdeleBaseChange
variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
attribute [local instance] Algebra.TensorProduct.rightAlgebra

theorem GroundTheory.Global.AdeleBaseChange.finiteTensorHomeomorph_apply (t : L ⊗[K] FiniteAdeleRing (𝓞 K) K) :
    finiteTensorHomeomorph K L t = finiteTensorEquiv K L t := by sorry

attribute [defeq] GroundTheory.Global.AdeleBaseChange.finiteTensorHomeomorph_apply
