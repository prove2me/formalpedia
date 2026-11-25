-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Parabolic_gradedJacquetMap_eq_zero_iff
-- name    : GroundTheory.Automorphic.Parabolic.gradedJacquetMap_eq_zero_iff
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T13:26:35.449783+00:00
-- url     : https://prove2.me/theorems/4877def4-06c0-57c8-8ff6-7d24fee7c58b
-- title:
--   Parabolic: graded Jacquet Map eq zero iff
-- statement:
--   The Parabolic construction uses the graded Jacquet Map eq zero iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GeometricLemmaGraded.lean#L240-L263
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GeometricLemmaGraded.lean#L240-L263

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_GeometricLemmaJacquetCell
import Definitions.Def_GroundTheory_AutomorphicForms_GeometricLemmaGraded
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

theorem GroundTheory.Automorphic.Parabolic.gradedJacquetMap_eq_zero_iff
    (hker : ∀ f : parabolicIndSpace F n β σ, f ∈ supportedIn σ Y →
      (∀ m ∈ levi F n γ, cellJacquet γ w σ f m = 0) →
      ∃ g : parabolicIndSpace F n β σ, g ∈ supportedIn σ (Y \ doubleCoset (permGL F w)
        (blockUpper F n β : Set (GL (Fin n) F)) (blockUpper F n γ)) ∧
        f - g ∈ Representation.Coinvariants.ker
          ((parabolicInd F n β σ).comp (unipotentRadical F n γ).subtype))
    (x : jacquetFiltration γ (σ := σ) Y) :
    gradedJacquetMap γ w σ hYo hCY hYQ x = 0 ↔
      (x : JacquetModule F n γ (parabolicInd F n β σ)) ∈ jacquetFiltration γ (σ := σ)
        (Y \ doubleCoset (permGL F w) (blockUpper F n β : Set (GL (Fin n) F)) (blockUpper F n γ)) := by sorry
