-- Prove2me | Theorems.Thm_GlobalTheory_CountId_vecMul_pow_Yb
-- name    : GlobalTheory.CountId.vecMul_pow_Yb
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T12:26:19.719248+00:00
-- url     : https://prove2.me/theorems/e4dcbbb2-2a63-4d5e-b011-845210918b66
-- title:
--   Count Id: vec Mul pow Yb
-- statement:
--   The Count Id construction uses the vec Mul pow Yb property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ToMatrixTwRight.lean#L142-L149
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ToMatrixTwRight.lean#L142-L149

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_LinearDescent
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_FourierMatch
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ToMatrixTwRight
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Module
noncomputable section
open GlobalTheory GlobalTheory.CountId
open GlobalTheory.JR
variable {n : ℕ} {E V : Type} [Field E] [AddCommGroup V] [Module E V]

theorem GlobalTheory.CountId.vecMul_pow_Yb (e : Basis (Fin n) E V) (T : V →ₗ[E] V) (l : V →ₗ[E] E) (i : ℕ) (j : Fin n) :
    ((fun j => l (e j)) ᵥ* (LinearMap.toMatrix e e T) ^ i) j = l ((T ^ i) (e j)) := by sorry
