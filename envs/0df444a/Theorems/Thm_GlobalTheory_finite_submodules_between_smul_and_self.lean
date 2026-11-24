-- Prove2me | Theorems.Thm_GlobalTheory_finite_submodules_between_smul_and_self
-- name    : GlobalTheory.finite_submodules_between_smul_and_self
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T22:47:10.84893+00:00
-- url     : https://prove2.me/theorems/b3ada93a-3073-427e-9c3a-1823bb554540
-- title:
--   Global Theory: finite submodules between smul and self
-- statement:
--   The Global Theory construction uses the finite submodules between smul and self property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/FiniteSubmodulesBetweenSmulAndSelf.lean#L17-L44
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/FiniteSubmodulesBetweenSmulAndSelf.lean#L17-L44

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_FiniteSubmodulesBetweenSmulAndSelf
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
open GlobalTheory

theorem GlobalTheory.finite_submodules_between_smul_and_self :
    ∀ (O A : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Finite (IsLocalRing.ResidueField O)] [AddCommGroup A] [Module O A] (C : Submodule O A), C.FG → ∀ c : O, c ≠ 0 → {N : Submodule O A | N ≤ C ∧ ∀ x ∈ C, c • x ∈ N}.Finite := by sorry
