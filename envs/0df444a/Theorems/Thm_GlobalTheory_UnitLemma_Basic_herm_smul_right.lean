-- Prove2me | Theorems.Thm_GlobalTheory_UnitLemma_Basic_herm_smul_right
-- name    : GlobalTheory.UnitLemma.Basic.herm_smul_right
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T15:15:36.945798+00:00
-- url     : https://prove2.me/theorems/4997f33a-2b99-47c6-ad55-b113f1283168
-- title:
--   Basic: herm smul right
-- statement:
--   The Basic construction uses the herm smul right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/ValIrreducible.lean#L50-L53
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/ValIrreducible.lean#L50-L53

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NLineOne
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_ValIrreducible
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Basic
variable {K : UQ} (B : InvAlg K)
variable {K : _root_.GlobalTheory.UnitLemma.UQ} (B : _root_.GlobalTheory.UnitLemma.InvAlg K)

theorem GlobalTheory.UnitLemma.Basic.herm_smul_right (x y z : B.A) (e : K.E) :
    B.herm x y (e • z) = K.c e * B.herm x y z := by sorry
