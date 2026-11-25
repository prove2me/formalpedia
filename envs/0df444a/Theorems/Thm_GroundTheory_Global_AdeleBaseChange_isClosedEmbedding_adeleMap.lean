-- Prove2me | Theorems.Thm_GroundTheory_Global_AdeleBaseChange_isClosedEmbedding_adeleMap
-- name    : GroundTheory.Global.AdeleBaseChange.isClosedEmbedding_adeleMap
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T08:25:32.996441+00:00
-- url     : https://prove2.me/theorems/40fadbe8-2c72-5160-9582-3c3d08e42daa
-- title:
--   Adele Base Change: is Closed Embedding adele Map
-- statement:
--   The Adele Base Change construction uses the is Closed Embedding adele Map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/Adele/BaseChange.lean#L164-L171
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/Adele/BaseChange.lean#L164-L171

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

theorem GroundTheory.Global.AdeleBaseChange.isClosedEmbedding_adeleMap : IsClosedEmbedding (adeleMap K L) := by sorry
