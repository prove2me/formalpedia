-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Parabolic_cellJacquet_eq_zero
-- name    : GroundTheory.Automorphic.Parabolic.cellJacquet_eq_zero
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T12:52:21.807232+00:00
-- url     : https://prove2.me/theorems/fedf730c-2b0a-57b5-8aae-8693690d57d0
-- title:
--   Parabolic: cell Jacquet eq zero
-- statement:
--   The Parabolic construction uses the cell Jacquet eq zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GeometricLemmaJacquetCell.lean#L316-L329
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GeometricLemmaJacquetCell.lean#L316-L329

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

theorem GroundTheory.Automorphic.Parabolic.cellJacquet_eq_zero {f : parabolicIndSpace F n β σ} (hf : f ∈ supportedIn σ Y)
    (hfC : ∀ g ∈ doubleCoset (permGL F w) (blockUpper F n β : Set (GL (Fin n) F))
      (blockUpper F n γ), (f : GL (Fin n) F → W) g = 0)
    {m : GL (Fin n) F} (hm : m ∈ levi F n γ) : cellJacquet γ w σ f m = 0 := by sorry
