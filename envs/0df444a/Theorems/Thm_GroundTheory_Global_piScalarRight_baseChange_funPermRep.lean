-- Prove2me | Theorems.Thm_GroundTheory_Global_piScalarRight_baseChange_funPermRep
-- name    : GroundTheory.Global.piScalarRight_baseChange_funPermRep
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T06:16:19.044205+00:00
-- url     : https://prove2.me/theorems/fb84f49a-cb1a-4ba6-aa50-87afafdf2720
-- title:
--   Global: pi Scalar Right base Change fun Perm Rep
-- statement:
--   The Global construction uses the pi Scalar Right base Change fun Perm Rep property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/HerbrandQuotients/UnitsHerbrandValue.lean#L13-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/HerbrandQuotients/UnitsHerbrandValue.lean#L13-L22

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_HerbrandQuotients_UnitsHerbrand
import Definitions.Def_GroundTheory_GlobalFields_HerbrandQuotients_UnitsHerbrandValue
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
open NumberField NumberField.Units NumberField.InfinitePlace MulAction Module
open scoped TensorProduct
noncomputable section
variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

theorem GroundTheory.Global.piScalarRight_baseChange_funPermRep {G X : Type*} [Group G] [MulAction G X] [Fintype X]
    [DecidableEq X] (g : G) (y : ℝ ⊗[ℤ] (X → ℤ)) :
    TensorProduct.piScalarRight ℤ ℝ ℝ X ((funPermRep ℤ G X g).baseChange ℝ y) =
      funPermRep ℝ G X g (TensorProduct.piScalarRight ℤ ℝ ℝ X y) := by sorry
