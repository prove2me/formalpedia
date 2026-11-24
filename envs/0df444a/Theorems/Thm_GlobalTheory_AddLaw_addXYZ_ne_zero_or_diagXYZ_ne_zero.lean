-- Prove2me | Theorems.Thm_GlobalTheory_AddLaw_addXYZ_ne_zero_or_diagXYZ_ne_zero
-- name    : GlobalTheory.AddLaw.addXYZ_ne_zero_or_diagXYZ_ne_zero
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T08:42:21.203804+00:00
-- url     : https://prove2.me/theorems/c574fa26-0d98-402c-a735-fa1d41e53522
-- title:
--   Add Law: add XYZ ne zero or diag XYZ ne zero
-- statement:
--   The Add Law construction uses the add XYZ ne zero or diag XYZ ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/AddXYZOrChordXYZOrOriginXYZNeZero.lean#L178-L182
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/AddXYZOrChordXYZOrOriginXYZNeZero.lean#L178-L182

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

theorem GlobalTheory.AddLaw.addXYZ_ne_zero_or_diagXYZ_ne_zero {P Q : Fin 3 → F} (hP : W.Nonsingular P)
    (hQ : W.Nonsingular Q) : W.addXYZ P Q ≠ 0 ∨ diagXYZ W P Q ≠ 0 := by sorry
