-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_GLnLocal_quotientEquivLattice_smul
-- name    : GroundTheory.Automorphic.GLnLocal.quotientEquivLattice_smul
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T12:52:34.760624+00:00
-- url     : https://prove2.me/theorems/972ac5c0-0a86-478d-93a6-2c63bdbb90fc
-- title:
--   GLn Local: quotient Equiv Lattice smul
-- statement:
--   The GLn Local construction uses the quotient Equiv Lattice smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GLnLattice.lean#L325-L330
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GLnLattice.lean#L325-L330

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

theorem GroundTheory.Automorphic.GLnLocal.quotientEquivLattice_smul (g : GL (Fin n) F) (x : GL (Fin n) F ⧸ integralGL F n) :
    quotientEquivLattice F n (g • x) = g • quotientEquivLattice F n x := by sorry
