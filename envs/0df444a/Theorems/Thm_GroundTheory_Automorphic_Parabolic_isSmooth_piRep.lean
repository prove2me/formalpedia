-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Parabolic_isSmooth_piRep
-- name    : GroundTheory.Automorphic.Parabolic.isSmooth_piRep
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T13:39:15.482818+00:00
-- url     : https://prove2.me/theorems/033b9070-6b29-4453-a438-1b4d1645b01c
-- title:
--   Parabolic: is Smooth pi Rep
-- statement:
--   The Parabolic construction uses the is Smooth pi Rep property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/CuspidalSplittingIsotypic.lean#L62-L70
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/CuspidalSplittingIsotypic.lean#L62-L70

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

theorem GroundTheory.Automorphic.Parabolic.isSmooth_piRep (hπ : IsSmooth π) (m : ℕ) : IsSmooth (piRep π m) := by sorry
