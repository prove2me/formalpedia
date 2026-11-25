-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Parabolic_isCompact_unipotentCompactG
-- name    : GroundTheory.Automorphic.Parabolic.isCompact_unipotentCompactG
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T11:33:24.229888+00:00
-- url     : https://prove2.me/theorems/a29857e4-37d3-42d7-9eb5-fe9dc11f8aad
-- title:
--   Parabolic: is Compact unipotent Compact G
-- statement:
--   The Parabolic construction uses the is Compact unipotent Compact G property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GeometricLemmaCompact.lean#L76-L79
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GeometricLemmaCompact.lean#L76-L79

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

theorem GroundTheory.Automorphic.Parabolic.isCompact_unipotentCompactG (e : ℕ) :
    IsCompact (unipotentCompactG (F := F) γ e : Set (GL (Fin n) F)) := by sorry
