-- Prove2me | Theorems.Thm_GlobalTheory_UnitLemma_InertUnit_charpoly_root
-- name    : GlobalTheory.UnitLemma.InertUnit.charpoly_root
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T21:27:12.693217+00:00
-- url     : https://prove2.me/theorems/4dc5fdad-d7f3-435e-8f73-c9283ef7a1a3
-- title:
--   Inert Unit: charpoly root
-- statement:
--   The Inert Unit construction uses the charpoly root property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsSelfReciprocalInvAlgWithPoly.lean#L75-L81
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsSelfReciprocalInvAlgWithPoly.lean#L75-L81

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsSelfReciprocalInvAlgWithPoly
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
open GlobalTheory GlobalTheory.UnitLemma
noncomputable section
open GlobalTheory.UnitLemma.InertUnit
variable {K : UQ} {P : K.E[X]}

theorem GlobalTheory.UnitLemma.InertUnit.charpoly_root (hP : P.Monic) (hr : C (K.c (P.coeff 0)) * P = (P.map (K.c : K.E →+* K.E)).reverse) :
    (invAlg hP hr).P = P := by sorry
