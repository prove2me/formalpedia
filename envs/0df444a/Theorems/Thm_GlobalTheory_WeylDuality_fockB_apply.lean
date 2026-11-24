-- Prove2me | Theorems.Thm_GlobalTheory_WeylDuality_fockB_apply
-- name    : GlobalTheory.WeylDuality.fockB_apply
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T21:55:49.710113+00:00
-- url     : https://prove2.me/theorems/af6b4a26-ac49-47dc-85d6-6d9ea91417f3
-- title:
--   Weyl Duality: fock B apply
-- statement:
--   The Weyl Duality construction uses the fock B apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ApplyWordMemDualWeyl.lean#L86-L86
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ApplyWordMemDualWeyl.lean#L86-L86

import Mathlib
import Definitions.Def_Formalism_GradedWeylDivisibility_StatementE
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ApplyWordMemDualWeyl
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial Formalism.GradedWeylDivisibility
noncomputable section
open GlobalTheory GlobalTheory.WeylDuality

theorem GlobalTheory.WeylDuality.fockB_apply {σ : Type} (f g : MvPolynomial σ ℚ) : fockB σ f g = fockQ f g := by sorry
