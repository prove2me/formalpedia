-- Prove2me | Theorems.Thm_GroundTheory_LocalField_PadicRank_finite_and_finrank_integer
-- name    : GroundTheory.LocalField.PadicRank.finite_and_finrank_integer
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T08:49:20.254583+00:00
-- url     : https://prove2.me/theorems/07e7709e-0720-4839-a966-94ffeb661c32
-- title:
--   Padic Rank: finite and finrank integer
-- statement:
--   The Padic Rank construction uses the finite and finrank integer property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/PrincipalUnitsRank.lean#L54-L71
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/PrincipalUnitsRank.lean#L54-L71

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

theorem GroundTheory.LocalField.PadicRank.finite_and_finrank_integer :
    Module.Finite ℤ_[p] 𝒪[K] ∧ Module.finrank ℤ_[p] 𝒪[K] =
      (letI := (CharZero.padicHom K p).toAlgebra; Module.finrank ℚ_[p] K) := by sorry
