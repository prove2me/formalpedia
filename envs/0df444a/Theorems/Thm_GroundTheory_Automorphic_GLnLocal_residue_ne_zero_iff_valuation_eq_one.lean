-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_GLnLocal_residue_ne_zero_iff_valuation_eq_one
-- name    : GroundTheory.Automorphic.GLnLocal.residue_ne_zero_iff_valuation_eq_one
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:41:17.4061+00:00
-- url     : https://prove2.me/theorems/685e9e3e-0687-4378-8ddd-3b438234d96f
-- title:
--   GLn Local: residue ne zero iff valuation eq one
-- statement:
--   The GLn Local construction uses the residue ne zero iff valuation eq one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/AffineBruhat.lean#L38-L42
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/AffineBruhat.lean#L38-L42

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

theorem GroundTheory.Automorphic.GLnLocal.residue_ne_zero_iff_valuation_eq_one (x : 𝒪[F]) :
    IsLocalRing.residue 𝒪[F] x ≠ 0 ↔ valuation F (x : F) = 1 := by sorry
