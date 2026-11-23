-- Prove2me | Theorems.Thm_GlobalTheory_CountId_repr_tw_apply
-- name    : GlobalTheory.CountId.repr_tw_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T21:02:27.806394+00:00
-- url     : https://prove2.me/theorems/6fb2a015-a739-408d-acce-96bd051a50ae
-- title:
--   Count Id: repr tw apply
-- statement:
--   The Count Id construction uses the repr tw apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ToMatrixTwRight.lean#L96-L98
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ToMatrixTwRight.lean#L96-L98

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

theorem GlobalTheory.CountId.repr_tw_apply (e : Basis (Fin n) E V) (γ : GL (Fin n) E) (i j : Fin n) :
    e.repr (tw e γ j) i = ((γ⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) i j := by sorry
