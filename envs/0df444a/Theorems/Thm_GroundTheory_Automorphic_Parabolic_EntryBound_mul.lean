-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Parabolic_EntryBound_mul
-- name    : GroundTheory.Automorphic.Parabolic.EntryBound.mul
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T11:33:17.265918+00:00
-- url     : https://prove2.me/theorems/b14b82a4-67df-46a5-bee8-45ce3b2143a7
-- title:
--   Entry Bound: mul
-- statement:
--   The Entry Bound construction uses the mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GeometricLemmaCompact.lean#L25-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GeometricLemmaCompact.lean#L25-L32

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

theorem GroundTheory.Automorphic.Parabolic.EntryBound.mul {a b : ℕ} {A B : Matrix (Fin n) (Fin n) F} (hA : EntryBound F a A)
    (hB : EntryBound F b B) : EntryBound F (a + b) (A * B) := by sorry
