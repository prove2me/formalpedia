-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Parabolic_indRep_mem_range_cellJacquetMap
-- name    : GroundTheory.Automorphic.Parabolic.indRep_mem_range_cellJacquetMap
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T13:09:27.931449+00:00
-- url     : https://prove2.me/theorems/f5dcd031-cc6c-42c8-be5e-dda669939a3a
-- title:
--   Parabolic: ind Rep mem range cell Jacquet Map
-- statement:
--   The Parabolic construction uses the ind Rep mem range cell Jacquet Map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GeometricLemmaCellSurjective.lean#L499-L505
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GeometricLemmaCellSurjective.lean#L499-L505

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
variable {β γ : Fin n → ℕ} {w : Equiv.Perm (Fin n)} {W : Type*} [AddCommGroup W] [Module ℂ W]
  {σ : Representation ℂ (levi F n β) W}
variable {Y : Set (GL (Fin n) F)} (hYo : IsOpen Y)
  (hCY : closure (doubleCoset (permGL F w) (blockUpper F n β : Set (GL (Fin n) F))
    (blockUpper F n γ)) ∩ Y = doubleCoset (permGL F w) (blockUpper F n β : Set (GL (Fin n) F))
    (blockUpper F n γ))
  (hYQ : ∀ g ∈ Y, ∀ q ∈ blockUpper F n γ, g * q ∈ Y)
include hYo hCY hYQ

theorem GroundTheory.Automorphic.Parabolic.indRep_mem_range_cellJacquetMap (m : levi F n γ)
    {ψ : indSpace (cellLeviSub F β γ w) (cellInducing β γ w σ)}
    (hψ : ψ ∈ LinearMap.range (cellJacquetMap γ w σ hYo hCY)) :
    indRep (cellLeviSub F β γ w) (cellInducing β γ w σ) m ψ ∈
      LinearMap.range (cellJacquetMap γ w σ hYo hCY) := by sorry
