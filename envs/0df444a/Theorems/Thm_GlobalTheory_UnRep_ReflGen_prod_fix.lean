-- Prove2me | Theorems.Thm_GlobalTheory_UnRep_ReflGen_prod_fix
-- name    : GlobalTheory.UnRep.ReflGen.prod_fix
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T21:23:32.021335+00:00
-- url     : https://prove2.me/theorems/5ea0c782-d8ff-438b-8e83-7c8d83fc48ce
-- title:
--   Refl Gen: prod fix
-- statement:
--   The Refl Gen construction uses the prod fix property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/UnitaryMatrixEqProdQuasiReflections.lean#L56-L66
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/UnitaryMatrixEqProdQuasiReflections.lean#L56-L66

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_IsHermForm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_UnitaryQuasiReflectionLawsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsAnisotropicOrthogonalBasisHermitianStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsQuasiReflectionProdMulVecEqStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_UnitaryMatrixEqProdQuasiReflections
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain GlobalTheory.AdLat GlobalTheory.UnRep
open scoped TensorProduct Matrix
open GlobalTheory GlobalTheory.UnRep GlobalTheory.UnRep.ReflGen
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {c : E ≃ₐ[F] E} {n : ℕ} {G : Matrix (Fin n) (Fin n) E}

theorem GlobalTheory.UnRep.ReflGen.prod_fix (hG : IsHermForm c G) (v : Fin n → E) (l : List ((Fin n → E) × E))
    (hl : ∀ p ∈ l, hermE c G p.1 p.1 ≠ 0 ∧ hermE c G v p.1 = 0) :
    (l.map fun p => refl c G p.1 p.2).prod *ᵥ v = v := by sorry
