-- Prove2me | Theorems.Thm_GroundTheory_Global_AdeleBaseChange_algebraMap_adeleRing
-- name    : GroundTheory.Global.AdeleBaseChange.algebraMap_adeleRing
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T08:24:30.602674+00:00
-- url     : https://prove2.me/theorems/19d3578b-c11c-5334-9031-b6ea3d618e1c
-- title:
--   Adele Base Change: algebra Map adele Ring
-- statement:
--   The Adele Base Change construction uses the algebra Map adele Ring property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/Adele/BaseChange.lean#L79-L80
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/Adele/BaseChange.lean#L79-L80

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

theorem GroundTheory.Global.AdeleBaseChange.algebraMap_adeleRing : algebraMap 𝔸[K] 𝔸[L] = adeleMap K L := by sorry
