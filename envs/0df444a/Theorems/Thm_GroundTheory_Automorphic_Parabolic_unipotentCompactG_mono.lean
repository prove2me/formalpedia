-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Parabolic_unipotentCompactG_mono
-- name    : GroundTheory.Automorphic.Parabolic.unipotentCompactG_mono
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T11:33:34.000224+00:00
-- url     : https://prove2.me/theorems/2639d064-9d1b-48df-a514-61978f38027a
-- title:
--   Parabolic: unipotent Compact G mono
-- statement:
--   The Parabolic construction uses the unipotent Compact G mono property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GeometricLemmaCompact.lean#L100-L145
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GeometricLemmaCompact.lean#L100-L145

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

theorem GroundTheory.Automorphic.Parabolic.unipotentCompactG_mono {e e' : ℕ} (h : e ≤ e') :
    unipotentCompactG (F := F) γ e ≤ unipotentCompactG γ e' := by sorry
