-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_GLnLocal_transvectionGL_mem
-- name    : GroundTheory.Automorphic.GLnLocal.transvectionGL_mem
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T23:29:53.826816+00:00
-- url     : https://prove2.me/theorems/23d6b47c-f82e-4f4f-9057-495e096f9c2e
-- title:
--   GLn Local: transvection GL mem
-- statement:
--   The GLn Local construction uses the transvection GL mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GLnLattice.lean#L174-L176
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GLnLattice.lean#L174-L176

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

theorem GroundTheory.Automorphic.GLnLocal.transvectionGL_mem {i j : Fin n} (hij : i ≠ j) : transvectionGL F n hij ∈ integralGL F n := by sorry
