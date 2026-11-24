-- Prove2me | Theorems.Thm_GlobalTheory_TraceIso_tr_prod
-- name    : GlobalTheory.TraceIso.tr_prod
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T21:11:12.105583+00:00
-- url     : https://prove2.me/theorems/b0e15f0b-0b4a-4d04-9f71-08a68890089e
-- title:
--   Trace Iso: tr prod
-- statement:
--   The Trace Iso construction uses the tr prod property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/NonemptyLinearEquivOfCharpolyEq.lean#L26-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/NonemptyLinearEquivOfCharpolyEq.lean#L26-L31

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NonemptyLinearEquivOfCharpolyEq
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.TraceIso
open Module
variable {k A : Type} [Field k] [Ring A] [Algebra k A]
variable {V W : Type} [AddCommGroup V] [Module k V] [Module A V] [IsScalarTower k A V]
  [AddCommGroup W] [Module k W] [Module A W] [IsScalarTower k A W]

theorem GlobalTheory.TraceIso.tr_prod [FiniteDimensional k V] [FiniteDimensional k W] (a : A) :
    tr k (V × W) a = tr k V a + tr k W a := by sorry
