-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Parabolic_EntryBound_leviProj
-- name    : GroundTheory.Automorphic.Parabolic.EntryBound.leviProj
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T11:32:05.499138+00:00
-- url     : https://prove2.me/theorems/363bb07e-1e12-5d57-9692-63a6206b5d33
-- title:
--   Entry Bound: levi Proj
-- statement:
--   The Entry Bound construction uses the levi Proj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GeometricLemmaCompact.lean#L41-L49
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GeometricLemmaCompact.lean#L41-L49

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

theorem GroundTheory.Automorphic.Parabolic.EntryBound.leviProj {γ : Fin n → ℕ} {e : ℕ} {p : blockUpper F n γ}
    (hp : EntryBound F e ((p : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)) :
    EntryBound F e (((leviProj F n γ p : levi F n γ) : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) := by sorry
