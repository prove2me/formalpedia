-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_GLnLocal_isLocallyProfinite
-- name    : GroundTheory.Automorphic.GLnLocal.isLocallyProfinite
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T12:53:07.4938+00:00
-- url     : https://prove2.me/theorems/fcfeb608-47de-459f-8b83-caff03c6a2e5
-- title:
--   GLn Local: is Locally Profinite
-- statement:
--   The GLn Local construction uses the is Locally Profinite property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GLnLocal.lean#L309-L312
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GLnLocal.lean#L309-L312

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_LocallyProfinite
import Definitions.Def_GroundTheory_AutomorphicForms_GLnLocal
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
open ValuativeRel Topology Filter Set
open GroundTheory.Automorphic.GLnLocal
variable (F : Type*) [Field F] [ValuativeRel F] (n : ℕ)
variable [TopologicalSpace F] [IsNonarchimedeanLocalField F]

theorem GroundTheory.Automorphic.GLnLocal.isLocallyProfinite :
    IsTopologicalGroup (GL (Fin n) F) ∧ LocallyCompactSpace (GL (Fin n) F) ∧
      T2Space (GL (Fin n) F) ∧ TotallyDisconnectedSpace (GL (Fin n) F) := by sorry
