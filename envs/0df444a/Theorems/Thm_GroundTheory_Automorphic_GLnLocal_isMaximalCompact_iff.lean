-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_GLnLocal_isMaximalCompact_iff
-- name    : GroundTheory.Automorphic.GLnLocal.isMaximalCompact_iff
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T12:53:06.544181+00:00
-- url     : https://prove2.me/theorems/ca9de4bc-1a9e-44f5-a9cc-436fcb4425e4
-- title:
--   GLn Local: is Maximal Compact iff
-- statement:
--   The GLn Local construction uses the is Maximal Compact iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GLnLattice.lean#L465-L489
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GLnLattice.lean#L465-L489

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_GLnLocal
import Definitions.Def_GroundTheory_AutomorphicForms_GLnLattice
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
open scoped Pointwise Matrix
open GroundTheory.Automorphic.GLnLocal
variable (F : Type*) [Field F] [ValuativeRel F] (n : ℕ)
variable [TopologicalSpace F] [IsNonarchimedeanLocalField F]

theorem GroundTheory.Automorphic.GLnLocal.isMaximalCompact_iff {H : Subgroup (GL (Fin n) F)} :
    IsMaximalCompact H ↔ ∃ g : GL (Fin n) F, H = (integralGL F n).map (MulAut.conj g).toMonoidHom := by sorry
