-- Prove2me | Theorems.Thm_GlobalTheory_UTrans_Chain_eventually_quad_ne
-- name    : GlobalTheory.UTrans.Chain.eventually_quad_ne
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:11:31.812029+00:00
-- url     : https://prove2.me/theorems/74fee598-6c29-4213-8fa0-57c0d2f8bffb
-- title:
--   Chain: eventually quad ne
-- statement:
--   The Chain construction uses the eventually quad ne property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/QuasiReflectionEqUnitaryTransvectionMul.lean#L13-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/QuasiReflectionEqUnitaryTransvectionMul.lean#L13-L32

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_IsHermHyperbolic
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ExistenceOfLattices_Hat1
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsIsotropicBasisNonorthogonalTwoVectorsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_UnitaryTransvectionSubmonoidNormalDetOneStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_QuasiReflectionEqMulTransvectionsOfHyperbolicPlaStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_QuasiReflectionEqUnitaryTransvectionMul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Matrix GlobalTheory.UTrans GlobalTheory.AdLat
open scoped TensorProduct
open GlobalTheory GlobalTheory.UTrans GlobalTheory.UTrans.Chain

theorem GlobalTheory.UTrans.Chain.eventually_quad_ne {E : Type} [Field E] [CharZero E] (a b c : E) (ha : a ≠ 0) :
    ∀ᶠ t : ℚ in Filter.cofinite, a + (t : E) * b + (t : E) ^ 2 * c ≠ 0 := by sorry
