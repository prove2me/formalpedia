-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Parabolic_coe_indCongr_apply
-- name    : GroundTheory.Automorphic.Parabolic.coe_indCongr_apply
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T12:57:31.531436+00:00
-- url     : https://prove2.me/theorems/bb410dec-1e0b-5e28-8633-7029256f5e50
-- title:
--   Parabolic: coe ind Congr apply
-- statement:
--   The Parabolic construction uses the coe ind Congr apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GeometricLemmaCharacters.lean#L312-L314
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GeometricLemmaCharacters.lean#L312-L314

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

theorem GroundTheory.Automorphic.Parabolic.coe_indCongr_apply (e : V₁ ≃ₗ[ℂ] V₂) (he : ∀ h v, e (ρ₁ h v) = ρ₂ h (e v))
    (φ : indSpace H ρ₁) (g : G) : ((indCongr e he φ : indSpace H ρ₂) : G → V₂) g = e ((φ : G → V₁) g) := by sorry
