-- Prove2me | Theorems.Thm_GlobalTheory_UTrans_isU_eq_tv_mul_tvGen
-- name    : GlobalTheory.UTrans.isU_eq_tv_mul_tvGen
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T21:23:11.190805+00:00
-- url     : https://prove2.me/theorems/d50c8aca-d687-4f8a-ac51-379fc9a1800d
-- title:
--   UTrans: is U eq tv mul tv Gen
-- statement:
--   The UTrans construction uses the is U eq tv mul tv Gen property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/UnitaryEqQuasiReflectionMulTransvections.lean#L62-L130
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/UnitaryEqQuasiReflectionMulTransvections.lean#L62-L130

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_IsHermHyperbolic
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ExistenceOfLattices_Hat1
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_IsHermForm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_UnitaryMatrixEqProdQuasiReflectionsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsAnisotropicOrthogonalBasisHermitian
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_TransvectionIdentitiesUnitaryStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_QuasiReflectionEqUnitaryTransvectionMul
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_UnitaryTransvectionSubmonoidNormalDetOneStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_UnitaryEqQuasiReflectionMulTransvections
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
open GlobalTheory GlobalTheory.UTrans
open NumberField IsDedekindDomain Matrix
open scoped TensorProduct

theorem GlobalTheory.UTrans.isU_eq_tv_mul_tvGen : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (c : E ≃ₐ[F] E) (n : ℕ) (G : Matrix (Fin n) (Fin n) E), _root_.GlobalTheory.UTrans.IsHerm (c : E →+* E) G → (∃ z : Fin n → E, z ≠ 0 ∧ _root_.GlobalTheory.UTrans.hf (c : E →+* E) G z z = 0) → ∀ γ, _root_.GlobalTheory.UTrans.IsU (c : E →+* E) G γ → (∀ x, _root_.GlobalTheory.UTrans.hf (c : E →+* E) G x x ≠ 0 → ∃ m ∈ _root_.GlobalTheory.UTrans.TvGen (c : E →+* E) G, γ = _root_.GlobalTheory.UTrans.tv (c : E →+* E) G x ((γ.det - 1) / _root_.GlobalTheory.UTrans.hf (c : E →+* E) G x x) * m) ∧ (γ.det = 1 → γ ∈ _root_.GlobalTheory.UTrans.TvGen (c : E →+* E) G) := by sorry
