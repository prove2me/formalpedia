-- Prove2me | Theorems.Thm_GlobalTheory_BoundedBasis_exists_generators_mod_smul
-- name    : GlobalTheory.BoundedBasis.exists_generators_mod_smul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T15:25:51.977788+00:00
-- url     : https://prove2.me/theorems/611416f4-1e21-4bfc-a383-184efaedea6b
-- title:
--   Bounded Basis: exists generators mod smul
-- statement:
--   The Bounded Basis construction uses the exists generators mod smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/ExistsFinsetTypesOfBoundedBases.lean#L13-L64
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/ExistsFinsetTypesOfBoundedBases.lean#L13-L64

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_IntegerApproximationCountHolds
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_ExistsFinsetTypesOfBoundedBases
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Matrix Module
open ReciprocityTheory.ChartRestriction.G.FD
open GlobalTheory
open GlobalTheory.BoundedBasis

theorem GlobalTheory.BoundedBasis.exists_generators_mod_smul {R : Type*} [CommRing R] [IsDedekindDomain R] {a : R}
    (ha : a ≠ 0) (r : ℕ) : ∀ (M : Type) [AddCommGroup M] [Module R M]
      (φ : M →ₗ[R] (Fin r → R)), Function.Injective φ →
      ∃ x : Fin r → M, ∀ m : M, ∃ (c : Fin r → R) (m' : M), m = ∑ i, c i • x i + a • m' := by sorry
