-- Prove2me | Theorems.Thm_GlobalTheory_T_exists_idealSheafData_of_isClopen_family
-- name    : GlobalTheory.T.exists_idealSheafData_of_isClopen_family
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T12:29:15.465106+00:00
-- url     : https://prove2.me/theorems/6667e2b1-ce43-414a-a8bd-220ff6391db6
-- title:
--   T: exists ideal Sheaf Data of is Clopen family
-- statement:
--   The T construction uses the exists ideal Sheaf Data of is Clopen family property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsIdealSheafDataOfIsClopenFamilyStatement.lean#L9-L14
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsIdealSheafDataOfIsClopenFamilyStatement.lean#L9-L14

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsIdealSheafDataOfIsClopenFamily
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_IsOpenOfMemIrreducibleComponentsOfFinite
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NormIdeal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FamIdeal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsIdealSheafDataOfIsClopenFamilyStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.exists_idealSheafData_of_isClopen_family : ∀ (Z : Scheme.{0}) (W : Set Z), IsClopen W → ∀ (F : ∀ U : Z.affineOpens, Ideal Γ(Z, U)),
    (∀ (U : Z.affineOpens) (f : Γ(Z, U)), (U : Set Z) ⊆ W →
      (F U).map (Z.presheaf.map (homOfLE (Z.basicOpen_le f)).op).hom = F (Z.affineBasicOpen f)) →
    ∃ J : Z.IdealSheafData, (∀ U : Z.affineOpens, (U : Set Z) ⊆ W → J.ideal U = F U) ∧
      (J.support : Set Z) ⊆ W := by sorry
