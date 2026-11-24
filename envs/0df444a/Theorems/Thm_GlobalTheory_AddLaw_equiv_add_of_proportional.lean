-- Prove2me | Theorems.Thm_GlobalTheory_AddLaw_equiv_add_of_proportional
-- name    : GlobalTheory.AddLaw.equiv_add_of_proportional
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T10:53:33.807036+00:00
-- url     : https://prove2.me/theorems/669465be-486f-499f-be97-7459078b3b09
-- title:
--   Add Law: equiv add of proportional
-- statement:
--   The Add Law construction uses the equiv add of proportional property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/AddXYZOrChordXYZOrOriginXYZNeZero.lean#L196-L201
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/AddXYZOrChordXYZOrOriginXYZNeZero.lean#L196-L201

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

theorem GlobalTheory.AddLaw.equiv_add_of_proportional {P Q T : Fin 3 → F} (hP : W.Nonsingular P) (hQ : W.Nonsingular Q)
    (h₁ : Proportional T (W.addXYZ P Q)) (h₂ : Proportional T (diagXYZ W P Q)) (hT : T ≠ 0) :
    T ≈ W.add P Q := by sorry
