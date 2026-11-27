-- Prove2me | Theorems.Thm_GlobalTheory_UnitLemma_Basic_herm_mul_left
-- name    : GlobalTheory.UnitLemma.Basic.herm_mul_left
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T12:42:09.015242+00:00
-- url     : https://prove2.me/theorems/25a0a12e-73f2-51e1-84ff-dc07bce181c4
-- title:
--   Basic: herm mul left
-- statement:
--   The Basic construction uses the herm mul left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/ValIrreducible.lean#L66-L71
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/ValIrreducible.lean#L66-L71

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

theorem GlobalTheory.UnitLemma.Basic.herm_mul_left (x u y z : B.A) :
    B.herm x (u * y) z = B.herm x y (B.σ u * z) := by sorry
