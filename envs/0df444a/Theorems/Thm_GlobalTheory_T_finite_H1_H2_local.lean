-- Prove2me | Theorems.Thm_GlobalTheory_T_finite_H1_H2_local
-- name    : GlobalTheory.T.finite_H1_H2_local
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T17:36:39.062477+00:00
-- url     : https://prove2.me/theorems/097dd3bf-b0d6-43fb-b154-f4797686a090
-- title:
--   T: finite H1 H2 local
-- statement:
--   The T construction uses the finite H1 H2 local property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/FiniteH1H2LocalStatement.lean#L6-L7
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/FiniteH1H2LocalStatement.lean#L6-L7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_FiniteH1H2Local
import Definitions.Def_Formalism_GaloisCohomology_LocalTateDualityK
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_FiniteH1H2LocalStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.GaloisCohomology ReciprocityTheory.Gal
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.finite_H1_H2_local : LocalTateDualityK → ∀ (l : ℕ) [Fact l.Prime] (K : IntermediateField ℚ_[l] (PadicAlgCl l)), FiniteDimensional ℚ_[l] K → ∀ (r : ℕ) (M : Type) [AddCommGroup M] [Module (ZMod (l ^ r)) M] [Finite M] [TopologicalSpace M] [DiscreteTopology M] (rho : Representation (ZMod (l ^ r)) (GK l K) M), 0 < r → ContAction rho → Finite (H1 rho) ∧ Finite (H2 rho) := by sorry
