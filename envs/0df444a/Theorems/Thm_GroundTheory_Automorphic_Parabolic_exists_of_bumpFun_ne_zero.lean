-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Parabolic_exists_of_bumpFun_ne_zero
-- name    : GroundTheory.Automorphic.Parabolic.exists_of_bumpFun_ne_zero
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T12:59:38.010063+00:00
-- url     : https://prove2.me/theorems/5008644e-6658-5e6e-b666-a97a926929ba
-- title:
--   Parabolic: exists of bump Fun ne zero
-- statement:
--   The Parabolic construction uses the exists of bump Fun ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GeometricLemmaCellSurjective.lean#L119-L123
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GeometricLemmaCellSurjective.lean#L119-L123

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_GeometricLemmaJacquetCell
import Definitions.Def_GroundTheory_AutomorphicForms_GeometricLemmaCellSurjective
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
variable {β : Fin n → ℕ} {W : Type*} [AddCommGroup W] [Module ℂ W]
  (σ : Representation ℂ (levi F n β) W)
variable {σ}

theorem GroundTheory.Automorphic.Parabolic.exists_of_bumpFun_ne_zero {x : GL (Fin n) F} {K : Subgroup (GL (Fin n) F)} {v : W}
    {g : GL (Fin n) F} (hg : bumpFun σ x K v g ≠ 0) :
    ∃ p : blockUpper F n β, ∃ k ∈ K, g = (p : GL (Fin n) F) * x * k := by sorry
