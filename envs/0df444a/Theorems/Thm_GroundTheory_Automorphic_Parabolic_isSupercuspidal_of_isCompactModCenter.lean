-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Parabolic_isSupercuspidal_of_isCompactModCenter
-- name    : GroundTheory.Automorphic.Parabolic.isSupercuspidal_of_isCompactModCenter
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T11:53:51.142829+00:00
-- url     : https://prove2.me/theorems/bdfc7b24-6088-4b26-8109-b259e3d251f4
-- title:
--   Parabolic: is Supercuspidal of is Compact Mod Center
-- statement:
--   The Parabolic construction uses the is Supercuspidal of is Compact Mod Center property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/SupercuspidalCoefficients.lean#L260-L395
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/SupercuspidalCoefficients.lean#L260-L395

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_JacquetAdmissible
import Definitions.Def_GroundTheory_AutomorphicForms_IwahoriFactorization
import Definitions.Def_GroundTheory_AutomorphicForms_SmoothRepContragredient
import Definitions.Def_GroundTheory_AutomorphicForms_SupercuspidalCoefficients
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.Automorphic
open GroundTheory.Automorphic.Parabolic
open Matrix Iwasawa GLnLocal ValuativeRel Topology Filter Set
open scoped Pointwise
variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {n : ℕ} {V : Type*} [AddCommGroup V] [Module ℂ V]
variable {π : Representation ℂ (GL (Fin n) F) V}

theorem GroundTheory.Automorphic.Parabolic.isSupercuspidal_of_isCompactModCenter (hπ : IsAdmissible π)
    (h : ∀ v : V, ∀ f ∈ smoothVectors (Representation.dual π),
      IsCompactModCenter (matrixCoeff π v f)) :
    IsSupercuspidal π := by sorry
