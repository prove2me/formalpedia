-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Parabolic_coe_cellJacquetMap_apply
-- name    : GroundTheory.Automorphic.Parabolic.coe_cellJacquetMap_apply
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T12:59:26.947705+00:00
-- url     : https://prove2.me/theorems/10cbd616-c4d7-4d6d-8f73-f105502127ca
-- title:
--   Parabolic: coe cell Jacquet Map apply
-- statement:
--   The Parabolic construction uses the coe cell Jacquet Map apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GeometricLemmaJacquetCell.lean#L534-L536
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GeometricLemmaJacquetCell.lean#L534-L536

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
variable (hYQ : ∀ g ∈ Y, ∀ q ∈ blockUpper F n γ, g * q ∈ Y)

theorem GroundTheory.Automorphic.Parabolic.coe_cellJacquetMap_apply (f : supportedIn σ Y) (m : levi F n γ) :
    (cellJacquetMap γ w σ hYo hCY f : levi F n γ → Representation.Coinvariants (cellRepA β γ w σ)) m =
      cellJacquet γ w σ (f : parabolicIndSpace F n β σ) m := by sorry
