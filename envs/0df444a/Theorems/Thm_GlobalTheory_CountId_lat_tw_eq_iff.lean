-- Prove2me | Theorems.Thm_GlobalTheory_CountId_lat_tw_eq_iff
-- name    : GlobalTheory.CountId.lat_tw_eq_iff
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T12:02:44.261737+00:00
-- url     : https://prove2.me/theorems/886bb121-32b6-570c-8f13-ba77cbe6149d
-- title:
--   Count Id: lat tw eq iff
-- statement:
--   The Count Id construction uses the lat tw eq iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ToMatrixTwRight.lean#L261-L280
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ToMatrixTwRight.lean#L261-L280

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

theorem GlobalTheory.CountId.lat_tw_eq_iff (e : Basis (Fin n) E V) (γ δ : GL (Fin n) E) :
    lat O (tw e δ) = lat O (tw e γ) ↔
      ∀ i j, ((δ * γ⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) i j ∈ (algebraMap O E).range ∧
        (((δ * γ⁻¹)⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) i j ∈ (algebraMap O E).range := by sorry
