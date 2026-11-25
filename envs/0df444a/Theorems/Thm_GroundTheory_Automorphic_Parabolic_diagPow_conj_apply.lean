-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Parabolic_diagPow_conj_apply
-- name    : GroundTheory.Automorphic.Parabolic.diagPow_conj_apply
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T11:38:39.641023+00:00
-- url     : https://prove2.me/theorems/137463c3-ed21-4877-9922-cdab50157e73
-- title:
--   Parabolic: diag Pow conj apply
-- statement:
--   The Parabolic construction uses the diag Pow conj apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/CuspidalAdmissible.lean#L70-L77
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/CuspidalAdmissible.lean#L70-L77

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
open Cartan

theorem GroundTheory.Automorphic.Parabolic.diagPow_conj_apply (μ : Fin n → ℤ) (g : GL (Fin n) F) (i j : Fin n) :
    (diagPow F n μ * g * (diagPow F n μ)⁻¹ : GL (Fin n) F) i j =
      (uniformizer F : F) ^ (μ i - μ j) * g i j := by sorry
