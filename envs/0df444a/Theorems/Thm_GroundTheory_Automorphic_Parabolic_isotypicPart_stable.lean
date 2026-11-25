-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Parabolic_isotypicPart_stable
-- name    : GroundTheory.Automorphic.Parabolic.isotypicPart_stable
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T13:34:13.136349+00:00
-- url     : https://prove2.me/theorems/e2de6373-cd91-4d5b-ade5-f044c7a48e1f
-- title:
--   Parabolic: isotypic Part stable
-- statement:
--   The Parabolic construction uses the isotypic Part stable property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/CuspidalSplittingIsotypic.lean#L226-L234
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/CuspidalSplittingIsotypic.lean#L226-L234

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

theorem GroundTheory.Automorphic.Parabolic.isotypicPart_stable (g : GL (Fin n) F) {u : U} (hu : u ∈ isotypicPart π ρ) :
    ρ g u ∈ isotypicPart π ρ := by sorry
