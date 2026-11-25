-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_GLnLocal_exists_valuation_div_zpow_eq_one
-- name    : GroundTheory.Automorphic.GLnLocal.exists_valuation_div_zpow_eq_one
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T23:31:03.335732+00:00
-- url     : https://prove2.me/theorems/d131bf70-d59b-4ff0-9895-d431c19e7b78
-- title:
--   GLn Local: exists valuation div zpow eq one
-- statement:
--   The GLn Local construction uses the exists valuation div zpow eq one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/AffineBruhat.lean#L522-L540
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/AffineBruhat.lean#L522-L540

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

theorem GroundTheory.Automorphic.GLnLocal.exists_valuation_div_zpow_eq_one {x : F} (hx : x ≠ 0) :
    ∃ m : ℤ, valuation F (x / ϖ ^ m) = 1 := by sorry
