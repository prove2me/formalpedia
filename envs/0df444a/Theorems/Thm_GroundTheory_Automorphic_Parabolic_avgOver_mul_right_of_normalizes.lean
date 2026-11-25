-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Parabolic_avgOver_mul_right_of_normalizes
-- name    : GroundTheory.Automorphic.Parabolic.avgOver_mul_right_of_normalizes
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T13:03:25.05936+00:00
-- url     : https://prove2.me/theorems/a63fb6bb-5d27-58e5-9520-a347333157ce
-- title:
--   Parabolic: avg Over mul right of normalizes
-- statement:
--   The Parabolic construction uses the avg Over mul right of normalizes property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GeometricLemmaCellKernel.lean#L146-L158
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GeometricLemmaCellKernel.lean#L146-L158

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_GeometricLemmaJacquetCell
import Definitions.Def_GroundTheory_AutomorphicForms_InductionJacquet
import Definitions.Def_GroundTheory_AutomorphicForms_GeometricLemmaCellKernel
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
  {n : ℕ} {β γ : Fin n → ℕ} {w : Equiv.Perm (Fin n)}
variable {G : Type*} [Group G] {W : Type*} [AddCommGroup W] [Module ℂ W]

theorem GroundTheory.Automorphic.Parabolic.avgOver_mul_right_of_normalizes {K : Subgroup G} {f : G → W} (hf : AvgFinite K f) {k : G}
    (hk : K.map (MulAut.conj k).toMonoidHom = K) (hkf : ∀ y, f (y * k) = f y) (y : G) :
    avgOver K f (y * k) = avgOver K f y := by sorry
