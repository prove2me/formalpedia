-- Prove2me | Theorems.Thm_GroundTheory_Global_AdeleBaseChange_adeleMap_injective
-- name    : GroundTheory.Global.AdeleBaseChange.adeleMap_injective
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T08:26:32.685317+00:00
-- url     : https://prove2.me/theorems/1d2e7a3d-c439-4e80-a2b9-6f8174d27bae
-- title:
--   Adele Base Change: adele Map injective
-- statement:
--   The Adele Base Change construction uses the adele Map injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/Adele/BaseChange.lean#L161-L162
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/Adele/BaseChange.lean#L161-L162

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

theorem GroundTheory.Global.AdeleBaseChange.adeleMap_injective : Function.Injective (adeleMap K L) := by sorry
