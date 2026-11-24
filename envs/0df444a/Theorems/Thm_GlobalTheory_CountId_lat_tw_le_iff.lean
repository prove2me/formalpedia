-- Prove2me | Theorems.Thm_GlobalTheory_CountId_lat_tw_le_iff
-- name    : GlobalTheory.CountId.lat_tw_le_iff
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T12:26:17.528671+00:00
-- url     : https://prove2.me/theorems/8690fea5-fa53-49a8-9bc5-ee74b6f97592
-- title:
--   Count Id: lat tw le iff
-- statement:
--   The Count Id construction uses the lat tw le iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ToMatrixTwRight.lean#L250-L259
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ToMatrixTwRight.lean#L250-L259

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

theorem GlobalTheory.CountId.lat_tw_le_iff (e : Basis (Fin n) E V) (γ : GL (Fin n) E) :
    lat O (tw e γ) ≤ lat O e ↔
      ∀ i j, ((γ⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) i j ∈ (algebraMap O E).range := by sorry
