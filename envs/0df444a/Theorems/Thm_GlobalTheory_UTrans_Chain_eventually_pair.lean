-- Prove2me | Theorems.Thm_GlobalTheory_UTrans_Chain_eventually_pair
-- name    : GlobalTheory.UTrans.Chain.eventually_pair
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T21:20:08.837621+00:00
-- url     : https://prove2.me/theorems/ca5a20d8-d00b-4bcc-9cd9-d9bd89341e6f
-- title:
--   Chain: eventually pair
-- statement:
--   The Chain construction uses the eventually pair property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/QuasiReflectionEqUnitaryTransvectionMul.lean#L60-L67
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/QuasiReflectionEqUnitaryTransvectionMul.lean#L60-L67

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

theorem GlobalTheory.UTrans.Chain.eventually_pair (σ : E →+* E) (G : Matrix (Fin n) (Fin n) E) (x w z : Fin n → E)
    (hx : hf σ G x z ≠ 0) :
    ∀ᶠ t : ℚ in Filter.cofinite, hf σ G (x + (t : E) • w) z ≠ 0 := by sorry
