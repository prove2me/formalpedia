-- Prove2me | Theorems.Thm_GlobalTheory_CountId_tw_repr
-- name    : GlobalTheory.CountId.tw_repr
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T21:02:05.277301+00:00
-- url     : https://prove2.me/theorems/6156f185-556b-4981-88cc-dce844084e30
-- title:
--   Count Id: tw repr
-- statement:
--   The Count Id construction uses the tw repr property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ToMatrixTwRight.lean#L100-L104
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ToMatrixTwRight.lean#L100-L104

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

theorem GlobalTheory.CountId.tw_repr (e : Basis (Fin n) E V) (γ : GL (Fin n) E) (y : V) :
    (fun i => (tw e γ).repr y i) = (γ : Matrix (Fin n) (Fin n) E) *ᵥ fun i => e.repr y i := by sorry
