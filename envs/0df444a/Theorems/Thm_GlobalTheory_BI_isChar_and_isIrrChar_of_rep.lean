-- Prove2me | Theorems.Thm_GlobalTheory_BI_isChar_and_isIrrChar_of_rep
-- name    : GlobalTheory.BI.isChar_and_isIrrChar_of_rep
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T03:52:47.028923+00:00
-- url     : https://prove2.me/theorems/700ea432-de80-4bf6-bca9-43615910a022
-- title:
--   BI: is Char and is Irr Char of rep
-- statement:
--   The BI construction uses the is Char and is Irr Char of rep property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CharacterTheory/IsCharacterOverSubfieldOfRepresentation.lean#L51-L67
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CharacterTheory/IsCharacterOverSubfieldOfRepresentation.lean#L51-L67

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_AbByPOfComm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_IsCharacterOverSubfieldOfRepresentation
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

theorem GlobalTheory.BI.isChar_and_isIrrChar_of_rep :
    ∀ (K L : Type) [Field K] [Field L] [Algebra K L] (G : Type) [Group G] (V : Type)
      [AddCommGroup V] [Module K V] [FiniteDimensional K V] (ρ : Representation K G V),
      _root_.GlobalTheory.BI.IsChar K L (fun g => algebraMap K L (ρ.character g)) ∧
        (ρ.IsIrreducible →
          _root_.GlobalTheory.BI.IsIrrChar K L (fun g => algebraMap K L (ρ.character g))) := by sorry
