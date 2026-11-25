-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Parabolic_entryBound_of_isCompact
-- name    : GroundTheory.Automorphic.Parabolic.entryBound_of_isCompact
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T11:39:25.906828+00:00
-- url     : https://prove2.me/theorems/32418671-6d30-47b3-9f4d-93012f6bd1c7
-- title:
--   Parabolic: entry Bound of is Compact
-- statement:
--   The Parabolic construction uses the entry Bound of is Compact property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GeometricLemmaCompact.lean#L34-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GeometricLemmaCompact.lean#L34-L39

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

theorem GroundTheory.Automorphic.Parabolic.entryBound_of_isCompact {S : Set (GL (Fin n) F)} (hS : IsCompact S) :
    ∃ e : ℕ, ∀ g ∈ S, EntryBound F e (g : Matrix (Fin n) (Fin n) F) ∧
      EntryBound F e ((g⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) := by sorry
