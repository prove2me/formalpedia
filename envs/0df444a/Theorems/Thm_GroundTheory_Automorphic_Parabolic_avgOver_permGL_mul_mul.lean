-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Parabolic_avgOver_permGL_mul_mul
-- name    : GroundTheory.Automorphic.Parabolic.avgOver_permGL_mul_mul
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T13:04:10.140673+00:00
-- url     : https://prove2.me/theorems/15a3aadf-63df-59ae-b734-80cb8ad59f6e
-- title:
--   Parabolic: avg Over perm GL mul mul
-- statement:
--   The Parabolic construction uses the avg Over perm GL mul mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GeometricLemmaCellKernel.lean#L175-L190
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GeometricLemmaCellKernel.lean#L175-L190

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
variable {W : Type*} [AddCommGroup W] [Module ℂ W] (σ : Representation ℂ (levi F n β) W)

theorem GroundTheory.Automorphic.Parabolic.avgOver_permGL_mul_mul (f : parabolicIndSpace F n β σ) {K : Subgroup (GL (Fin n) F)}
    (hf : AvgFinite K (f : GL (Fin n) F → W)) {t : GL (Fin n) F}
    (ht : K.map (MulAut.conj t).toMonoidHom = K) (u : GL (Fin n) F) :
    avgOver K (f : GL (Fin n) F → W) (permGL F w * u * t) = avgOver K (cellFun w σ f t) u := by sorry
