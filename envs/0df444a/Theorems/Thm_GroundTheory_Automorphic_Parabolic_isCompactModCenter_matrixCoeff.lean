-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Parabolic_isCompactModCenter_matrixCoeff
-- name    : GroundTheory.Automorphic.Parabolic.isCompactModCenter_matrixCoeff
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T11:53:47.350961+00:00
-- url     : https://prove2.me/theorems/62baa634-2a83-4ec0-8942-1296ec984125
-- title:
--   Parabolic: is Compact Mod Center matrix Coeff
-- statement:
--   The Parabolic construction uses the is Compact Mod Center matrix Coeff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/SupercuspidalCoefficients.lean#L109-L233
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/SupercuspidalCoefficients.lean#L109-L233

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

theorem GroundTheory.Automorphic.Parabolic.isCompactModCenter_matrixCoeff (hπ : IsSmooth π) (hsc : IsSupercuspidal π) (v : V)
    {f : Module.Dual ℂ V} (hf : f ∈ smoothVectors (Representation.dual π)) :
    IsCompactModCenter (matrixCoeff π v f) := by sorry
