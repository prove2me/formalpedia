-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Parabolic_exists_avgOver_cellFun_eq_zero
-- name    : GroundTheory.Automorphic.Parabolic.exists_avgOver_cellFun_eq_zero
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T13:03:06.709358+00:00
-- url     : https://prove2.me/theorems/6ae6a9d6-5012-54e2-935f-1993fe9b6a34
-- title:
--   Parabolic: exists avg Over cell Fun eq zero
-- statement:
--   The Parabolic construction uses the exists avg Over cell Fun eq zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GeometricLemmaCellKernel.lean#L49-L138
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GeometricLemmaCellKernel.lean#L49-L138

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

theorem GroundTheory.Automorphic.Parabolic.exists_avgOver_cellFun_eq_zero (hσ : IsSmooth σ) {Y : Set (GL (Fin n) F)}
    (hYo : IsOpen Y)
    (hCY : closure (doubleCoset (permGL F w) (blockUpper F n β : Set (GL (Fin n) F))
      (blockUpper F n γ)) ∩ Y = doubleCoset (permGL F w) (blockUpper F n β : Set (GL (Fin n) F))
      (blockUpper F n γ))
    {f : parabolicIndSpace F n β σ} (hf : f ∈ supportedIn σ Y) {t : GL (Fin n) F}
    (ht : t ∈ levi F n γ) (h0 : cellJacquet γ w σ f t = 0) :
    ∃ e : ℕ, CellSupp γ w σ f t (unipotentCompactG γ e) ∧
      avgOver (unipotentCompactG γ e) (cellFun w σ f t) 1 = 0 := by sorry
