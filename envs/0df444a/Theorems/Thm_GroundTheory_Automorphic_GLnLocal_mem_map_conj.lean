-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_GLnLocal_mem_map_conj
-- name    : GroundTheory.Automorphic.GLnLocal.mem_map_conj
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T23:29:42.720272+00:00
-- url     : https://prove2.me/theorems/d2bd4beb-92c6-4246-97e9-ceda99cc3680
-- title:
--   GLn Local: mem map conj
-- statement:
--   The GLn Local construction uses the mem map conj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GLnLattice.lean#L428-L439
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GLnLattice.lean#L428-L439

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
omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]

theorem GroundTheory.Automorphic.GLnLocal.mem_map_conj {g x : GL (Fin n) F} {H : Subgroup (GL (Fin n) F)} :
    x ∈ H.map (MulAut.conj g).toMonoidHom ↔ g⁻¹ * x * g ∈ H := by sorry
