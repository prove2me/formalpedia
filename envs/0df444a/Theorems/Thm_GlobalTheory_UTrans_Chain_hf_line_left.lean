-- Prove2me | Theorems.Thm_GlobalTheory_UTrans_Chain_hf_line_left
-- name    : GlobalTheory.UTrans.Chain.hf_line_left
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:11:10.137498+00:00
-- url     : https://prove2.me/theorems/d246ab5d-c853-4712-a4f3-637416cba41b
-- title:
--   Chain: hf line left
-- statement:
--   The Chain construction uses the hf line left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/QuasiReflectionEqUnitaryTransvectionMul.lean#L36-L40
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/QuasiReflectionEqUnitaryTransvectionMul.lean#L36-L40

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
variable {E : Type} [Field E] [CharZero E] {n : ℕ}

theorem GlobalTheory.UTrans.Chain.hf_line_left (σ : E →+* E) (G : Matrix (Fin n) (Fin n) E) (x w z : Fin n → E) (t : E) :
    hf σ G (x + t • w) z = hf σ G x z + t * hf σ G w z := by sorry
