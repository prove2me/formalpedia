-- Prove2me | Theorems.Thm_GlobalTheory_KernelTri_kernel_trilinear_apply
-- name    : GlobalTheory.KernelTri.kernel_trilinear_apply
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T12:15:15.171511+00:00
-- url     : https://prove2.me/theorems/c5181bdd-c5d2-46ca-a0e7-98da1cc07a23
-- title:
--   Kernel Tri: kernel trilinear apply
-- statement:
--   The Kernel Tri construction uses the kernel trilinear apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/LocalTrilinearFormUnique.lean#L80-L83
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/LocalTrilinearFormUnique.lean#L80-L83

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_IndicatorFunctionIdentity
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_KernelsCommuteTwistedStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_LocalTrilinearFormUnique
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.IndefiniteRowSideFullHecke.IndicatorFunctionIdentity ValuativeRel IsLocalRing
noncomputable section
noncomputable section
open GlobalTheory GlobalTheory.KernelTri

theorem GlobalTheory.KernelTri.kernel_trilinear_apply {V' A B V : Type} [AddCommGroup V'] [Module ℂ V'] [AddCommGroup A] [Module ℂ A]
    [AddCommGroup B] [Module ℂ B] [AddCommGroup V] [Module ℂ V] (θ : V' →ₗ[ℂ] A →ₗ[ℂ] B →ₗ[ℂ] V)
    (p : Submodule ℂ (B →ₗ[ℂ] V)) (hmem : ∀ v a, θ v a ∈ p) (v : V') (a : A) :
    (th1 θ p hmem v a).1 = θ v a := by sorry

attribute [defeq] GlobalTheory.KernelTri.kernel_trilinear_apply
