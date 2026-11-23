-- Prove2me | Theorems.Thm_GlobalTheory_BI_isChar_baseChange
-- name    : GlobalTheory.BI.isChar_baseChange
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:21:02.509279+00:00
-- url     : https://prove2.me/theorems/a492f35d-8539-49df-a924-0d97df1c124b
-- title:
--   BI: is Char base Change
-- statement:
--   The BI construction uses the is Char base Change property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CharacterTheory/CharacterExtendScalarsRep.lean#L31-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CharacterTheory/CharacterExtendScalarsRep.lean#L31-L36

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_AbByPOfComm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_CharacterExtendScalarsRep
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.BI
noncomputable section
open GlobalTheory GlobalTheory.BI

theorem GlobalTheory.BI.isChar_baseChange : ∀ (K L : Type) [Field K] [Field L] [Algebra K L] (G : Type) [Group G]
    (χ : G → L), IsChar K L χ → IsChar L L χ := by sorry
