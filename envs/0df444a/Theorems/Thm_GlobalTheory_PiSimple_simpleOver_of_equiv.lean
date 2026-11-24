-- Prove2me | Theorems.Thm_GlobalTheory_PiSimple_simpleOver_of_equiv
-- name    : GlobalTheory.PiSimple.simpleOver_of_equiv
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:29:16.760053+00:00
-- url     : https://prove2.me/theorems/499bd55a-e5ba-43c5-8c6c-fad309123d9c
-- title:
--   Pi Simple: simple Over of equiv
-- statement:
--   The Pi Simple construction uses the simple Over of equiv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/SimpleOverStableSubmodulePiTensor.lean#L12-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/SimpleOverStableSubmodulePiTensor.lean#L12-L31

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_SimpleOverStableSubmoduleTensorPureKernelSpanStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_OperatorStablePiTensorPureKernelSpanStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_SimpleOver
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_SimpleOverStableSubmodulePiTensor
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped TensorProduct
open GlobalTheory GlobalTheory.PiSimple
open GlobalTheory.TensHead

theorem GlobalTheory.PiSimple.simpleOver_of_equiv {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W]
    [Module ℂ W] (e : V ≃ₗ[ℂ] W) (G : Set (Module.End ℂ V)) (G' : Set (Module.End ℂ W))
    (K : Submodule ℂ V) (K' : Submodule ℂ W) (hK : K.map (e : V →ₗ[ℂ] W) = K')
    (hG : ∀ g' ∈ G', ∃ g ∈ G, ∀ x, g' (e x) = e (g x)) (h : SimpleOver G' K') :
    SimpleOver G K := by sorry
