-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_GLnLocal_transvection_mem_integer
-- name    : GroundTheory.Automorphic.GLnLocal.transvection_mem_integer
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T23:29:58.209903+00:00
-- url     : https://prove2.me/theorems/24b60880-6f25-46d1-832a-954961f2e8f4
-- title:
--   GLn Local: transvection mem integer
-- statement:
--   The GLn Local construction uses the transvection mem integer property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GLnLattice.lean#L156-L165
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GLnLattice.lean#L156-L165

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

theorem GroundTheory.Automorphic.GLnLocal.transvection_mem_integer {i j : Fin n} {c : F} (hc : c ∈ 𝒪[F]) (a b : Fin n) :
    Matrix.transvection i j c a b ∈ 𝒪[F] := by sorry
