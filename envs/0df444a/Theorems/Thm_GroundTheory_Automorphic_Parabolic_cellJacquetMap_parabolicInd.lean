-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Parabolic_cellJacquetMap_parabolicInd
-- name    : GroundTheory.Automorphic.Parabolic.cellJacquetMap_parabolicInd
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T13:01:06.396789+00:00
-- url     : https://prove2.me/theorems/6a6e7b50-0b3b-473d-8975-2a343b682935
-- title:
--   Parabolic: cell Jacquet Map parabolic Ind
-- statement:
--   The Parabolic construction uses the cell Jacquet Map parabolic Ind property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GeometricLemmaCellSurjective.lean#L490-L497
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GeometricLemmaCellSurjective.lean#L490-L497

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_GeometricLemmaJacquetCell
import Definitions.Def_GroundTheory_AutomorphicForms_GeometricLemmaCellSurjective
import Theorems.Thm_GroundTheory_Automorphic_Parabolic_supportedIn_le_comap

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
variable {β γ : Fin n → ℕ} {w : Equiv.Perm (Fin n)} {W : Type*} [AddCommGroup W] [Module ℂ W]
  {σ : Representation ℂ (levi F n β) W}
variable {Y : Set (GL (Fin n) F)} (hYo : IsOpen Y)
  (hCY : closure (doubleCoset (permGL F w) (blockUpper F n β : Set (GL (Fin n) F))
    (blockUpper F n γ)) ∩ Y = doubleCoset (permGL F w) (blockUpper F n β : Set (GL (Fin n) F))
    (blockUpper F n γ))
  (hYQ : ∀ g ∈ Y, ∀ q ∈ blockUpper F n γ, g * q ∈ Y)
include hYo hCY hYQ

theorem GroundTheory.Automorphic.Parabolic.cellJacquetMap_parabolicInd (f : supportedIn σ Y) (m : levi F n γ) :
    cellJacquetMap γ w σ hYo hCY ⟨parabolicInd F n β σ m f,
      supportedIn_le_comap γ hYQ (levi_le_blockUpper m.2) f.2⟩ =
      indRep (cellLeviSub F β γ w) (cellInducing β γ w σ) m (cellJacquetMap γ w σ hYo hCY f) := by sorry
