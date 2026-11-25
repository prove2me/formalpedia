-- Prove2me | Theorems.Thm_GlobalTheory_CountId_lat_stable_iff
-- name    : GlobalTheory.CountId.lat_stable_iff
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T12:03:01.009941+00:00
-- url     : https://prove2.me/theorems/d727ebd2-1d25-4760-9f47-d71781bd96e8
-- title:
--   Count Id: lat stable iff
-- statement:
--   The Count Id construction uses the lat stable iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ToMatrixTwRight.lean#L225-L236
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ToMatrixTwRight.lean#L225-L236

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

theorem GlobalTheory.CountId.lat_stable_iff (e : Basis (Fin n) E V) (T : V →ₗ[E] V) :
    (∀ y ∈ lat O e, T y ∈ lat O e) ↔ ∀ i j, LinearMap.toMatrix e e T i j ∈ (algebraMap O E).range := by sorry
