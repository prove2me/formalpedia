-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Parabolic_exists_sub_mem_ker_of_cellJacquet_eq_zero
-- name    : GroundTheory.Automorphic.Parabolic.exists_sub_mem_ker_of_cellJacquet_eq_zero
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T13:03:52.864664+00:00
-- url     : https://prove2.me/theorems/94a85aa8-6939-5433-a9e2-7110643871b1
-- title:
--   Parabolic: exists sub mem ker of cell Jacquet eq zero
-- statement:
--   The Parabolic construction uses the exists sub mem ker of cell Jacquet eq zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GeometricLemmaCellKernel.lean#L192-L349
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GeometricLemmaCellKernel.lean#L192-L349

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

theorem GroundTheory.Automorphic.Parabolic.exists_sub_mem_ker_of_cellJacquet_eq_zero (hσ : IsSmooth σ) {Y : Set (GL (Fin n) F)}
    (hYo : IsOpen Y)
    (hCY : closure (doubleCoset (permGL F w) (blockUpper F n β : Set (GL (Fin n) F))
      (blockUpper F n γ)) ∩ Y = doubleCoset (permGL F w) (blockUpper F n β : Set (GL (Fin n) F))
      (blockUpper F n γ))
    (hYQ : ∀ g ∈ Y, ∀ q ∈ blockUpper F n γ, g * q ∈ Y)
    {f : parabolicIndSpace F n β σ} (hf : f ∈ supportedIn σ Y)
    (h0 : ∀ m ∈ levi F n γ, cellJacquet γ w σ f m = 0) :
    ∃ g : parabolicIndSpace F n β σ,
      g ∈ supportedIn σ (Y \ doubleCoset (permGL F w) (blockUpper F n β : Set (GL (Fin n) F))
        (blockUpper F n γ)) ∧
      f - g ∈ Representation.Coinvariants.ker
        ((parabolicInd F n β σ).comp (unipotentRadical F n γ).subtype) := by sorry
