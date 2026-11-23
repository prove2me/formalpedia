-- Prove2me | Theorems.Thm_GlobalTheory_AddLaw_ne_zero_of_nonsingular
-- name    : GlobalTheory.AddLaw.ne_zero_of_nonsingular
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T11:46:30.496382+00:00
-- url     : https://prove2.me/theorems/3d0fa602-bb04-477b-9815-88cd5b69cb32
-- title:
--   Add Law: ne zero of nonsingular
-- statement:
--   The Add Law construction uses the ne zero of nonsingular property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/AddXYZOrChordXYZOrOriginXYZNeZero.lean#L106-L108
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/AddXYZOrChordXYZOrOriginXYZNeZero.lean#L106-L108

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

theorem GlobalTheory.AddLaw.ne_zero_of_nonsingular {P : Fin 3 → F} (hP : W.Nonsingular P) : P ≠ 0 := by sorry
