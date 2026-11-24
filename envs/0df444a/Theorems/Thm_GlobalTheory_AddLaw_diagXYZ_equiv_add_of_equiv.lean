-- Prove2me | Theorems.Thm_GlobalTheory_AddLaw_diagXYZ_equiv_add_of_equiv
-- name    : GlobalTheory.AddLaw.diagXYZ_equiv_add_of_equiv
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T11:47:19.313554+00:00
-- url     : https://prove2.me/theorems/e4ac0fdc-2cf9-4f54-a0ac-db7bc4b422ec
-- title:
--   Add Law: diag XYZ equiv add of equiv
-- statement:
--   The Add Law construction uses the diag XYZ equiv add of equiv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/AddXYZOrChordXYZOrOriginXYZNeZero.lean#L164-L171
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/AddXYZOrChordXYZOrOriginXYZNeZero.lean#L164-L171

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_DiagZEqNegAddY
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_SubMulOriginD
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_AddXYZOrChordXYZOrOriginXYZNeZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open WeierstrassCurve WeierstrassCurve.Projective
open GlobalTheory GlobalTheory.AddLaw
variable {F : Type*} [Field F] {W : Projective F}

theorem GlobalTheory.AddLaw.diagXYZ_equiv_add_of_equiv {P Q : Fin 3 → F} (hP : W.Equation P) (h : P ≈ Q) :
    diagXYZ W P Q ≈ W.add P Q := by sorry
