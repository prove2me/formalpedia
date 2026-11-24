-- Prove2me | Theorems.Thm_GlobalTheory_T_powIndex_torsion_ker_range_mul
-- name    : GlobalTheory.T.powIndex_torsion_ker_range_mul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T09:07:02.720842+00:00
-- url     : https://prove2.me/theorems/1cf61faa-1f8a-498e-908e-ebb7fbc64538
-- title:
--   T: pow Index torsion ker range mul
-- statement:
--   The T construction uses the pow Index torsion ker range mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/PowIndexTorsionKerRangeMulStatement.lean#L7-L8
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/PowIndexTorsionKerRangeMulStatement.lean#L7-L8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_PowIndexTorsionKerRangeMul
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_MemPowSub
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_PowIndexTorsionKerRangeMulStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Polynomial GlobalTheory.QNorm GlobalTheory.CNorm
open scoped WithZero TensorProduct
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.powIndex_torsion_ker_range_mul : ∀ (p : ℕ) (A A' : Type) [CommGroup A] [CommGroup A'] (g : A →* A'), pIdx p g.ker ≠ 0 → pTor p g.ker ≠ 0 → pIdx p g.range ≠ 0 → pTor p g.range ≠ 0 → pIdx p (⊤ : Subgroup A) ≠ 0 ∧ pTor p (⊤ : Subgroup A) ≠ 0 ∧ pIdx p (⊤ : Subgroup A) * pTor p g.ker * pTor p g.range = pIdx p g.ker * pIdx p g.range * pTor p (⊤ : Subgroup A) := by sorry
