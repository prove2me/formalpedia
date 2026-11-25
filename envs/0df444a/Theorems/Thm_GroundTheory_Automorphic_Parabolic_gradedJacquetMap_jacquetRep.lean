-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Parabolic_gradedJacquetMap_jacquetRep
-- name    : GroundTheory.Automorphic.Parabolic.gradedJacquetMap_jacquetRep
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T13:03:31.923531+00:00
-- url     : https://prove2.me/theorems/0d6ec440-656f-568c-b1c0-9e30cacebd9d
-- title:
--   Parabolic: graded Jacquet Map jacquet Rep
-- statement:
--   The Parabolic construction uses the graded Jacquet Map jacquet Rep property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GeometricLemmaGraded.lean#L206-L225
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GeometricLemmaGraded.lean#L206-L225

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_GeometricLemmaJacquetCell
import Definitions.Def_GroundTheory_AutomorphicForms_GeometricLemmaGraded
import Theorems.Thm_GroundTheory_Automorphic_Parabolic_jacquetFiltration_le_comap

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
  {W : Type*} [AddCommGroup W] [Module ℂ W] (σ : Representation ℂ (levi F n β) W)
variable {Y : Set (GL (Fin n) F)} (hYo : IsOpen Y)
  (hCY : closure (doubleCoset (permGL F w) (blockUpper F n β : Set (GL (Fin n) F))
    (blockUpper F n γ)) ∩ Y = doubleCoset (permGL F w) (blockUpper F n β : Set (GL (Fin n) F))
    (blockUpper F n γ))
  (hYQ : ∀ g ∈ Y, ∀ q ∈ blockUpper F n γ, g * q ∈ Y)

theorem GroundTheory.Automorphic.Parabolic.gradedJacquetMap_jacquetRep (m : levi F n γ) (x : jacquetFiltration γ (σ := σ) Y) :
    gradedJacquetMap γ w σ hYo hCY hYQ
        ⟨jacquetRep F n γ (parabolicInd F n β σ) m x, jacquetFiltration_le_comap γ hYQ m x.2⟩ =
      invSqrtModular F n γ (leviIncl m) •
        indRep (cellLeviSub F β γ w) (cellInducing β γ w σ) m (gradedJacquetMap γ w σ hYo hCY hYQ x) := by sorry
