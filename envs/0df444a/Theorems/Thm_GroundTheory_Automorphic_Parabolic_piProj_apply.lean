-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Parabolic_piProj_apply
-- name    : GroundTheory.Automorphic.Parabolic.piProj_apply
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T13:30:53.671876+00:00
-- url     : https://prove2.me/theorems/036ea930-f775-557f-8fbc-13a34a1f731c
-- title:
--   Parabolic: pi Proj apply
-- statement:
--   The Parabolic construction uses the pi Proj apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/CuspidalSplittingIsotypic.lean#L96-L96
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/CuspidalSplittingIsotypic.lean#L96-L96

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_CuspidalSplittingProjective
import Definitions.Def_GroundTheory_AutomorphicForms_CuspidalSplittingIsotypic
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Automorphic
open GroundTheory.Automorphic.Parabolic
open Function Topology
variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {n : ℕ}
variable {V U : Type*} [AddCommGroup V] [Module ℂ V] [AddCommGroup U] [Module ℂ U]
  {π : Representation ℂ (GL (Fin n) F) V} {ρ : Representation ℂ (GL (Fin n) F) U}
  {ω : GL (Fin n) F → ℂ}
omit [ValuativeRel F] [IsNonarchimedeanLocalField F] [TopologicalSpace F]

theorem GroundTheory.Automorphic.Parabolic.piProj_apply (m : ℕ) (i : Fin m) (x : Fin m → V) : piProj π m i x = x i := by sorry
