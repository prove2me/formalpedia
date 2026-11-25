-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Parabolic_unipotentCompactG_eq
-- name    : GroundTheory.Automorphic.Parabolic.unipotentCompactG_eq
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T11:38:50.380349+00:00
-- url     : https://prove2.me/theorems/5067e218-249f-52c3-a8c4-415657e37cfb
-- title:
--   Parabolic: unipotent Compact G eq
-- statement:
--   The Parabolic construction uses the unipotent Compact G eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GeometricLemmaCompact.lean#L81-L86
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GeometricLemmaCompact.lean#L81-L86

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
variable (γ : Fin n → ℕ)
variable {γ}

theorem GroundTheory.Automorphic.Parabolic.unipotentCompactG_eq (e : ℕ) :
    unipotentCompactG (F := F) γ e = unipotentRadical F n γ ⊓
      (integralGL F n).comap (MulAut.conj (rankTorus F n γ e)).toMonoidHom := by sorry
