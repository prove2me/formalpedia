-- Prove2me | Theorems.Thm_GlobalTheory_AnArc_l_eq_zero_of_forall_smul_mem
-- name    : GlobalTheory.AnArc.l_eq_zero_of_forall_smul_mem
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T13:28:54.804868+00:00
-- url     : https://prove2.me/theorems/c645455e-0fcf-4d19-9869-20c847931013
-- title:
--   An Arc: l eq zero of forall smul mem
-- statement:
--   The An Arc construction uses the l eq zero of forall smul mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/SmulPeriodMapMkZeroFstEqNegForm.lean#L152-L155
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/SmulPeriodMapMkZeroFstEqNegForm.lean#L152-L155

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ArchimedeanThetaValues_DegeneratingToriPeriodMapEqBaseOfYEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_TorusProjPeriodZeroEqReal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_SmulPeriodMapMkZeroFstEqNegForm
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped TensorProduct
open GlobalTheory
open GlobalTheory.AnArc
variable {O : Type} [CommRing O] [StarRing O] (A : AnArc O)

theorem GlobalTheory.AnArc.l_eq_zero_of_forall_smul_mem {v : A.La} (hv : v.y = 0) (h : ∀ s : ℂ, (s • A.P0 v).2 ∈ A.abelian₂) : v.l = 0 := by sorry
