-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_GLnLocal_residue_eq_zero_iff_valuation_lt_one
-- name    : GroundTheory.Automorphic.GLnLocal.residue_eq_zero_iff_valuation_lt_one
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:40:51.307376+00:00
-- url     : https://prove2.me/theorems/5b65d0ec-70f9-4916-b4f3-51eba0d57c37
-- title:
--   GLn Local: residue eq zero iff valuation lt one
-- statement:
--   The GLn Local construction uses the residue eq zero iff valuation lt one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/AffineBruhat.lean#L32-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/AffineBruhat.lean#L32-L36

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_GLnLocal
import Definitions.Def_GroundTheory_AutomorphicForms_GLnLattice
import Definitions.Def_GroundTheory_AutomorphicForms_FiniteBruhat
import Definitions.Def_GroundTheory_AutomorphicForms_AffineBruhat
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
open Matrix DoubleCoset ValuativeRel
open GroundTheory.Automorphic.GLnLocal
variable (F : Type*) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  (n : ℕ)
local notation "ϖ" => ((uniformizer F : 𝒪[F]) : F)

theorem GroundTheory.Automorphic.GLnLocal.residue_eq_zero_iff_valuation_lt_one (x : 𝒪[F]) :
    IsLocalRing.residue 𝒪[F] x = 0 ↔ valuation F (x : F) < 1 := by sorry
