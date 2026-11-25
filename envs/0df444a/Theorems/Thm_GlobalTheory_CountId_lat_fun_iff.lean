-- Prove2me | Theorems.Thm_GlobalTheory_CountId_lat_fun_iff
-- name    : GlobalTheory.CountId.lat_fun_iff
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T12:02:57.670481+00:00
-- url     : https://prove2.me/theorems/9f3060e9-0a4d-5736-b681-263e956a2d3f
-- title:
--   Count Id: lat fun iff
-- statement:
--   The Count Id construction uses the lat fun iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ToMatrixTwRight.lean#L238-L248
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ToMatrixTwRight.lean#L238-L248

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
variable (O : Type) [CommRing O] [Algebra O E] [Module O V] [IsScalarTower O E V]
variable [IsDomain O] [Module.IsTorsionFree O E]

theorem GlobalTheory.CountId.lat_fun_iff (e : Basis (Fin n) E V) (l : V →ₗ[E] E) :
    (∀ y ∈ lat O e, l y ∈ (algebraMap O E).range) ↔ ∀ j, l (e j) ∈ (algebraMap O E).range := by sorry
