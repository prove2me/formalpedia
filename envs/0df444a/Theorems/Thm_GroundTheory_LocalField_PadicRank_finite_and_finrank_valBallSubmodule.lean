-- Prove2me | Theorems.Thm_GroundTheory_LocalField_PadicRank_finite_and_finrank_valBallSubmodule
-- name    : GroundTheory.LocalField.PadicRank.finite_and_finrank_valBallSubmodule
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T08:48:42.554005+00:00
-- url     : https://prove2.me/theorems/897c46f9-be00-57a4-80a2-c367fd95a7cc
-- title:
--   Padic Rank: finite and finrank val Ball Submodule
-- statement:
--   The Padic Rank construction uses the finite and finrank val Ball Submodule property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/PrincipalUnitsRank.lean#L131-L136
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/PrincipalUnitsRank.lean#L131-L136

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_PadicLogLinear
import Definitions.Def_GroundTheory_LocalFields_Integers
import Definitions.Def_GroundTheory_LocalFields_PrincipalUnitsRank
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.LocalField
open ValuativeRel IsLocalRing Topology Filter
open scoped WithZero
variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
open GroundTheory.LocalField.PadicRank
variable (p : ℕ) [hp : Fact p.Prime]
variable [CharP 𝓀[K] p] [CharZero K]
attribute [local instance] algebraK algebraInteger

theorem GroundTheory.LocalField.PadicRank.finite_and_finrank_valBallSubmodule (m : ℤ) :
    Module.Finite ℤ_[p] (valBallSubmodule K p m) ∧ Module.finrank ℤ_[p] (valBallSubmodule K p m) =
      (letI := (CharZero.padicHom K p).toAlgebra; Module.finrank ℚ_[p] K) := by sorry
