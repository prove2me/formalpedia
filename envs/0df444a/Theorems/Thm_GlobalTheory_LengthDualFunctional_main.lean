-- Prove2me | Theorems.Thm_GlobalTheory_LengthDualFunctional_main
-- name    : GlobalTheory.LengthDualFunctional.main
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T08:43:40.719377+00:00
-- url     : https://prove2.me/theorems/7bfe455d-1613-46ca-b20e-f1d9ec564549
-- title:
--   Length Dual Functional: main
-- statement:
--   The Length Dual Functional construction uses the main property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/ExistsDualNeZeroCompEqZero.lean#L26-L44
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/ExistsDualNeZeroCompEqZero.lean#L26-L44

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsDualNeZeroCompEqZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u_1 u_2
open GlobalTheory GlobalTheory.LengthDualFunctional
open Module

theorem GlobalTheory.LengthDualFunctional.main : ∀ {R : Type u_1} [inst : CommRing R] [inst_1 : IsDomain R] [IsDiscreteValuationRing R] {M : Type u_2} [inst_3 : AddCommGroup M] [inst_4 : Module R M] [Module.Free R M] [Module.Finite R M] {f : M →ₗ[R] M}, (LinearMap.det : (M →ₗ[R] M) → R) f = (0 : R) → Module.length R (M ⧸ LinearMap.range f) = ⊤ := by sorry
