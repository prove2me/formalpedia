-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Parabolic_gap_or_bounded
-- name    : GroundTheory.Automorphic.Parabolic.gap_or_bounded
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T11:38:13.905017+00:00
-- url     : https://prove2.me/theorems/7c7bbfc5-2cf7-5916-b9dc-dd9eaa34ad9b
-- title:
--   Parabolic: gap or bounded
-- statement:
--   The Parabolic construction uses the gap or bounded property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/CuspidalAdmissible.lean#L139-L184
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/CuspidalAdmissible.lean#L139-L184

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_LeviCartan
import Definitions.Def_GroundTheory_AutomorphicForms_SmoothRepSchur
import Definitions.Def_GroundTheory_AutomorphicForms_MeasuresModulus
import Definitions.Def_GroundTheory_AutomorphicForms_CuspidalAdmissible
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.Automorphic
open GroundTheory.Automorphic.Parabolic
open Matrix Iwasawa GLnLocal ValuativeRel Topology Filter Set
variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {n : ℕ} {α : Type*} [LinearOrder α] {β : Fin n → α}

theorem GroundTheory.Automorphic.Parabolic.gap_or_bounded (μ : Fin n → ℤ) {C : ℤ} (hC : 0 < C) :
    (∃ θ : ℤ, ∃ b : α, (∃ j, β j = b ∧ θ ≤ μ j) ∧ (∃ k, β k = b ∧ μ k < θ) ∧
      ∀ k, β k = b → μ k < θ → μ k + C ≤ θ) ∨
    (∀ i j, β i = β j → μ i < μ j + n * C) := by sorry
