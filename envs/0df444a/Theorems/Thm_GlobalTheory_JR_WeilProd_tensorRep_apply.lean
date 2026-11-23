-- Prove2me | Theorems.Thm_GlobalTheory_JR_WeilProd_tensorRep_apply
-- name    : GlobalTheory.JR.WeilProd.tensorRep_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T20:52:59.412805+00:00
-- url     : https://prove2.me/theorems/f8e64554-03a4-44fd-8a80-63119e798184
-- title:
--   Weil Prod: tensor Rep apply
-- statement:
--   The Weil Prod construction uses the tensor Rep apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/TensorRepApply.lean#L10-L12
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/TensorRepApply.lean#L10-L12

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_IsTestRep
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_TensorRepApply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.JR GlobalTheory.JR.WeilProd

theorem GlobalTheory.JR.WeilProd.tensorRep_apply {G H X Y : Type} (W₁ : G → (X → ℂ) → X → ℂ) (W₂ : H → (Y → ℂ) → Y → ℂ) (g : G × H)
    (f : X × Y → ℂ) (p : X × Y) :
    tensorRep W₁ W₂ g f p = W₁ g.1 (fun u => W₂ g.2 (fun v => f (u, v)) p.2) p.1 := by sorry
