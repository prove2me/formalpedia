-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Parabolic_isOpen_conj_integralGL
-- name    : GroundTheory.Automorphic.Parabolic.isOpen_conj_integralGL
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T11:33:25.581546+00:00
-- url     : https://prove2.me/theorems/3313627f-0da7-44b6-9c85-9e03f3e2c49e
-- title:
--   Parabolic: is Open conj integral GL
-- statement:
--   The Parabolic construction uses the is Open conj integral GL property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GeometricLemmaCompact.lean#L88-L91
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GeometricLemmaCompact.lean#L88-L91

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

theorem GroundTheory.Automorphic.Parabolic.isOpen_conj_integralGL (t : GL (Fin n) F) :
    IsOpen (((integralGL F n).comap (MulAut.conj t).toMonoidHom : Subgroup (GL (Fin n) F)) :
      Set (GL (Fin n) F)) := by sorry
