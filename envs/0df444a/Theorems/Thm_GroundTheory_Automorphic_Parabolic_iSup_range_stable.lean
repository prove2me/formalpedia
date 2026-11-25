-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Parabolic_iSup_range_stable
-- name    : GroundTheory.Automorphic.Parabolic.iSup_range_stable
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T13:31:43.704669+00:00
-- url     : https://prove2.me/theorems/5ee4dfc7-4ae2-449c-9daf-ee817f39457b
-- title:
--   Parabolic: i Sup range stable
-- statement:
--   The Parabolic construction uses the i Sup range stable property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/CuspidalSplittingIsotypic.lean#L138-L151
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/CuspidalSplittingIsotypic.lean#L138-L151

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
omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]

theorem GroundTheory.Automorphic.Parabolic.iSup_range_stable (s : Finset (Representation.IntertwiningMap π ρ))
    (g : GL (Fin n) F) {y : U}
    (hy : y ∈ ⨆ t ∈ s, LinearMap.range (t : Representation.IntertwiningMap π ρ).toLinearMap) :
    ρ g y ∈ ⨆ t ∈ s, LinearMap.range (t : Representation.IntertwiningMap π ρ).toLinearMap := by sorry
