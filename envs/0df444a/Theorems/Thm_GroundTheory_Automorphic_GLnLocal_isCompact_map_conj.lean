-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_GLnLocal_isCompact_map_conj
-- name    : GroundTheory.Automorphic.GLnLocal.isCompact_map_conj
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T23:30:00.306281+00:00
-- url     : https://prove2.me/theorems/6930961a-bdbb-448d-a83d-95c04ad8d9f1
-- title:
--   GLn Local: is Compact map conj
-- statement:
--   The GLn Local construction uses the is Compact map conj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GLnLattice.lean#L441-L448
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GLnLattice.lean#L441-L448

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

theorem GroundTheory.Automorphic.GLnLocal.isCompact_map_conj (g : GL (Fin n) F) {H : Subgroup (GL (Fin n) F)}
    (hH : IsCompact (H : Set (GL (Fin n) F))) :
    IsCompact (H.map (MulAut.conj g).toMonoidHom : Set (GL (Fin n) F)) := by sorry
