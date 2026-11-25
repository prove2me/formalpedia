-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Parabolic_cellJacquet_parabolicInd
-- name    : GroundTheory.Automorphic.Parabolic.cellJacquet_parabolicInd
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T12:52:02.108701+00:00
-- url     : https://prove2.me/theorems/bffb93fe-6376-5e32-9248-179c08ad6837
-- title:
--   Parabolic: cell Jacquet parabolic Ind
-- statement:
--   The Parabolic construction uses the cell Jacquet parabolic Ind property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GeometricLemmaJacquetCell.lean#L289-L298
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GeometricLemmaJacquetCell.lean#L289-L298

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_GeometricLemmaCellGroups
import Definitions.Def_GroundTheory_AutomorphicForms_GeometricLemmaCount
import Definitions.Def_GroundTheory_AutomorphicForms_GeometricLemmaJacquetCell
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
open Matrix Iwasawa GLnLocal ValuativeRel Topology Set DoubleCoset Filter
variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {n : ℕ} {β γ : Fin n → ℕ} {w : Equiv.Perm (Fin n)}
variable {W : Type*} [AddCommGroup W] [Module ℂ W] (σ : Representation ℂ (levi F n β) W)
variable {Y : Set (GL (Fin n) F)} (hYo : IsOpen Y)
  (hCY : closure (doubleCoset (permGL F w) (blockUpper F n β : Set (GL (Fin n) F))
    (blockUpper F n γ)) ∩ Y = doubleCoset (permGL F w) (blockUpper F n β : Set (GL (Fin n) F))
    (blockUpper F n γ))
include hYo hCY
omit hYo hCY

theorem GroundTheory.Automorphic.Parabolic.cellJacquet_parabolicInd (f : parabolicIndSpace F n β σ) (m₀ m : GL (Fin n) F) :
    cellJacquet γ w σ (parabolicInd F n β σ m₀ f) m = cellJacquet γ w σ f (m * m₀) := by sorry
