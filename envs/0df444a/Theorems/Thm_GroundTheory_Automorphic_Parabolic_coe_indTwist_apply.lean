-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Parabolic_coe_indTwist_apply
-- name    : GroundTheory.Automorphic.Parabolic.coe_indTwist_apply
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T13:04:38.634725+00:00
-- url     : https://prove2.me/theorems/d4e2e255-cf0d-46bb-bde3-2ea48d8548a1
-- title:
--   Parabolic: coe ind Twist apply
-- statement:
--   The Parabolic construction uses the coe ind Twist apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GeometricLemmaCharacters.lean#L354-L357
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GeometricLemmaCharacters.lean#L354-L357

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_GeometricLemmaJacquetCell
import Definitions.Def_GroundTheory_AutomorphicForms_CuspidalAdmissible
import Definitions.Def_GroundTheory_AutomorphicForms_JacquetAdmissible
import Definitions.Def_GroundTheory_AutomorphicForms_GeometricLemmaCharacters
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
set_option linter.unusedSectionVars false
open GroundTheory GroundTheory.Automorphic
open GroundTheory.Automorphic.Parabolic
open Matrix Iwasawa GLnLocal ValuativeRel Topology Set DoubleCoset Filter
variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {n : ℕ}
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] {H : Subgroup G}
  {V₁ V₂ : Type*} [AddCommGroup V₁] [Module ℂ V₁] [AddCommGroup V₂] [Module ℂ V₂]
  {ρ₁ : Representation ℂ H V₁} {ρ₂ : Representation ℂ H V₂}
variable {V : Type*} [AddCommGroup V] [Module ℂ V] {ρ : Representation ℂ H V}

theorem GroundTheory.Automorphic.Parabolic.coe_indTwist_apply (χ : G →* ℂ) (hχ : ∀ g, χ g ≠ 0)
    (hχo : ∃ U : Subgroup G, IsOpen (U : Set G) ∧ ∀ u ∈ U, χ u = 1) (φ : indSpace H ρ) (g : G) :
    ((indTwist χ hχ hχo φ : indSpace H (twist (χ.comp H.subtype) ρ)) : G → V) g =
      χ g • (φ : G → V) g := by sorry
