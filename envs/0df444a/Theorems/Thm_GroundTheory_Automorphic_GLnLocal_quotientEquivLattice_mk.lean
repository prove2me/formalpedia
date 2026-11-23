-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_GLnLocal_quotientEquivLattice_mk
-- name    : GroundTheory.Automorphic.GLnLocal.quotientEquivLattice_mk
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T05:24:42.618152+00:00
-- url     : https://prove2.me/theorems/95eaaa67-1d14-4f58-85fa-6fc80d39505f
-- title:
--   GLn Local: quotient Equiv Lattice mk
-- statement:
--   The GLn Local construction uses the quotient Equiv Lattice mk property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GLnLattice.lean#L321-L323
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GLnLattice.lean#L321-L323

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

theorem GroundTheory.Automorphic.GLnLocal.quotientEquivLattice_mk (g : GL (Fin n) F) :
    quotientEquivLattice F n (g : GL (Fin n) F ⧸ integralGL F n) = g • standard F n := by sorry

attribute [defeq] GroundTheory.Automorphic.GLnLocal.quotientEquivLattice_mk
