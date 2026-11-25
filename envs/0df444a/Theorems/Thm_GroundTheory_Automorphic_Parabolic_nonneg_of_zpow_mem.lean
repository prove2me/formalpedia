-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Parabolic_nonneg_of_zpow_mem
-- name    : GroundTheory.Automorphic.Parabolic.nonneg_of_zpow_mem
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T11:56:29.757932+00:00
-- url     : https://prove2.me/theorems/5b04ddec-ac66-434b-a70e-803be9acd130
-- title:
--   Parabolic: nonneg of zpow mem
-- statement:
--   The Parabolic construction uses the nonneg of zpow mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/SupercuspidalCoefficients.lean#L254-L258
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/SupercuspidalCoefficients.lean#L254-L258

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_JacquetAdmissible
import Definitions.Def_GroundTheory_AutomorphicForms_IwahoriFactorization
import Definitions.Def_GroundTheory_AutomorphicForms_SmoothRepContragredient
import Definitions.Def_GroundTheory_AutomorphicForms_SupercuspidalCoefficients
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
open scoped Pointwise
variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {n : ℕ} {V : Type*} [AddCommGroup V] [Module ℂ V]
variable {π : Representation ℂ (GL (Fin n) F) V}

theorem GroundTheory.Automorphic.Parabolic.nonneg_of_zpow_mem {z : ℤ} (h : (uniformizer F : F) ^ z ∈ 𝒪[F]) : 0 ≤ z := by sorry
