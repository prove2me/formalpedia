-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Parabolic_sqrtModular_leviIncl_of_mem
-- name    : GroundTheory.Automorphic.Parabolic.sqrtModular_leviIncl_of_mem
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T11:47:43.898663+00:00
-- url     : https://prove2.me/theorems/ccd700bc-5b27-5491-93b1-4842a8eb2b57
-- title:
--   Parabolic: sqrt Modular levi Incl of mem
-- statement:
--   The Parabolic construction uses the sqrt Modular levi Incl of mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/JacquetAdmissible.lean#L127-L150
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/JacquetAdmissible.lean#L127-L150

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_CuspidalAdmissible
import Definitions.Def_GroundTheory_AutomorphicForms_AdmissibleInduction
import Definitions.Def_GroundTheory_AutomorphicForms_JacquetAdmissible
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
open Matrix Iwasawa GLnLocal ValuativeRel Topology Filter Set MeasureTheory Measure
variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {n : ℕ} {α : Type*} [LinearOrder α] {β : Fin n → α}

theorem GroundTheory.Automorphic.Parabolic.sqrtModular_leviIncl_of_mem {γ : Fin n → ℕ} (m : levi F n β)
    (hm : (m : GL (Fin n) F) ∈ unipotentRadical F n γ) :
    sqrtModular F n β (leviIncl m) = 1 := by sorry
