-- Prove2me | Theorems.Thm_GlobalTheory_AddLaw_diagXYZ_ne_zero_of_equiv
-- name    : GlobalTheory.AddLaw.diagXYZ_ne_zero_of_equiv
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T10:53:18.247802+00:00
-- url     : https://prove2.me/theorems/f8a0e311-ad51-4ebf-bd7e-953e9322419c
-- title:
--   Add Law: diag XYZ ne zero of equiv
-- statement:
--   The Add Law construction uses the diag XYZ ne zero of equiv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/AddXYZOrChordXYZOrOriginXYZNeZero.lean#L173-L176
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/AddXYZOrChordXYZOrOriginXYZNeZero.lean#L173-L176

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

theorem GlobalTheory.AddLaw.diagXYZ_ne_zero_of_equiv {P Q : Fin 3 → F} (hP : W.Nonsingular P) (hQ : W.Nonsingular Q)
    (h : P ≈ Q) : diagXYZ W P Q ≠ 0 := by sorry
