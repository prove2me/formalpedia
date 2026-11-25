-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Parabolic_diagPow_mem_center
-- name    : GroundTheory.Automorphic.Parabolic.diagPow_mem_center
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T11:38:44.187085+00:00
-- url     : https://prove2.me/theorems/7ca287b9-17b2-4388-8bfc-e4297983e72d
-- title:
--   Parabolic: diag Pow mem center
-- statement:
--   The Parabolic construction uses the diag Pow mem center property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/CuspidalAdmissible.lean#L86-L99
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/CuspidalAdmissible.lean#L86-L99

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

theorem GroundTheory.Automorphic.Parabolic.diagPow_mem_center {c : Fin n → ℤ} (hc : ∀ i j, β i = β j → c i = c j) :
    (⟨diagPow F n c, diagPow_mem_levi c⟩ : levi F n β) ∈ Submonoid.center (levi F n β) := by sorry
