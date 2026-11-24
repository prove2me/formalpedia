-- Prove2me | Theorems.Thm_GlobalTheory_UnitLemma_exists_invAlg_root
-- name    : GlobalTheory.UnitLemma.exists_invAlg_root
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T21:37:42.41347+00:00
-- url     : https://prove2.me/theorems/d7215633-8740-4e5d-a98b-2574f3819d26
-- title:
--   Unit Lemma: exists inv Alg root
-- statement:
--   The Unit Lemma construction uses the exists inv Alg root property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsSelfReciprocalInvAlgWithPoly.lean#L86-L93
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsSelfReciprocalInvAlgWithPoly.lean#L86-L93

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
open InertUnit

theorem GlobalTheory.UnitLemma.exists_invAlg_root : ∀ (K : GlobalTheory.UnitLemma.UQ) (P : K.E[X]), P.Monic →
    C (K.c (P.coeff 0)) * P = (P.map (K.c : K.E →+* K.E)).reverse →
    ∃ B : GlobalTheory.UnitLemma.InvAlg K, B.g * B.σ B.g = 1 ∧ B.P = P := by sorry
