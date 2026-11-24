-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_mem_formGroup
-- name    : GroundTheory.Automorphic.mem_formGroup
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T23:35:45.934804+00:00
-- url     : https://prove2.me/theorems/d21c7014-5e31-4ca3-81f1-05fd47801eb1
-- title:
--   Automorphic: mem form Group
-- statement:
--   The Automorphic construction uses the mem form Group property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/AdelicDixmierMalliavinLie.lean#L67-L67
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/AdelicDixmierMalliavinLie.lean#L67-L67

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_RealGroupsLie
import Definitions.Def_GroundTheory_AutomorphicForms_AdelicDixmierMalliavinLie
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Automorphic
open scoped Manifold ContDiff Topology
open NormedSpace Set
set_option linter.unusedSectionVars false
noncomputable section
variable {𝔄 : Type*} [NormedRing 𝔄] [NormedAlgebra ℝ 𝔄] [CompleteSpace 𝔄] [FiniteDimensional ℝ 𝔄]
  (σ : 𝔄 →ₗ[ℝ] 𝔄) (hσ1 : σ 1 = 1) (hσ : ∀ x y, σ (x * y) = σ y * σ x) (J : 𝔄ˣ)

theorem GroundTheory.Automorphic.mem_formGroup {g : 𝔄ˣ} : g ∈ formGroup σ hσ1 hσ J ↔ σ g * J * g = J := by sorry
