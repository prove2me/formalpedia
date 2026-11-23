-- Prove2me | Theorems.Thm_GlobalTheory_coe_modNEquivTorsion_mk
-- name    : GlobalTheory.coe_modNEquivTorsion_mk
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T11:05:15.706119+00:00
-- url     : https://prove2.me/theorems/8f6394e1-70af-4145-8c15-6e7ed4a0f07d
-- title:
--   Global Theory: coe mod NEquiv Torsion mk
-- statement:
--   The Global Theory construction uses the coe mod NEquiv Torsion mk property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ExistsUniqueRealLinearOfEventuallyAddModDiscrete.lean#L346-L348
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ExistsUniqueRealLinearOfEventuallyAddModDiscrete.lean#L346-L348

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_TendstoUniformlyOnDoublingLogOfContraction
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsUniqueRealLinearOfEventuallyAddModDiscrete
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Topology Set
open GlobalTheory
variable (K : Type*) [DivisionRing K] [CharZero K] {M : Type*} [AddCommGroup M] [Module K M]
  (Λ : Submodule ℤ M) (n : ℕ) [NeZero n]

theorem GlobalTheory.coe_modNEquivTorsion_mk (x : Λ) :
    (modNEquivTorsion K Λ n (Submodule.Quotient.mk x) : M ⧸ Λ) =
      Submodule.Quotient.mk ((n : K)⁻¹ • (x : M)) := by sorry

attribute [defeq] GlobalTheory.coe_modNEquivTorsion_mk
