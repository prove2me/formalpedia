-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Parabolic_exists_isCompact_support_doubleCoset
-- name    : GroundTheory.Automorphic.Parabolic.exists_isCompact_support_doubleCoset
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T11:33:15.882486+00:00
-- url     : https://prove2.me/theorems/86e5c251-4526-4350-a693-a327594956c1
-- title:
--   Parabolic: exists is Compact support double Coset
-- statement:
--   The Parabolic construction uses the exists is Compact support double Coset property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GeometricLemmaCompact.lean#L180-L222
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GeometricLemmaCompact.lean#L180-L222

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_GeometricLemmaFiltration
import Definitions.Def_GroundTheory_AutomorphicForms_GeometricLemmaOrbit
import Definitions.Def_GroundTheory_AutomorphicForms_AdmissibleInduction
import Definitions.Def_GroundTheory_AutomorphicForms_GeometricLemmaCompact
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
open Matrix Iwasawa GLnLocal ValuativeRel Topology Set DoubleCoset
variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {n : ℕ}
variable {β γ : Fin n → ℕ} {W : Type*} [AddCommGroup W] [Module ℂ W]
  {σ : Representation ℂ (levi F n β) W}
variable (w : Equiv.Perm (Fin n))

theorem GroundTheory.Automorphic.Parabolic.exists_isCompact_support_doubleCoset {Y : Set (GL (Fin n) F)} (hYo : IsOpen Y)
    (hCY : closure (doubleCoset (permGL F w) (blockUpper F n β : Set (GL (Fin n) F))
      (blockUpper F n γ)) ∩ Y = doubleCoset (permGL F w) (blockUpper F n β : Set (GL (Fin n) F))
      (blockUpper F n γ))
    {f : parabolicIndSpace F n β σ} (hf : f ∈ supportedIn σ Y) :
    ∃ L : Set (GL (Fin n) F), IsCompact L ∧ L ⊆ blockUpper F n γ ∧
      ∀ q ∈ blockUpper F n γ, (f : GL (Fin n) F → W) (permGL F w * q) ≠ 0 →
        ∃ x ∈ blockUpper F n γ, permGL F w * x * (permGL F w)⁻¹ ∈ blockUpper F n β ∧
          ∃ l ∈ L, q = x * l := by sorry
