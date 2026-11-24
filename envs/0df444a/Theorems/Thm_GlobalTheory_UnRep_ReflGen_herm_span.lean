-- Prove2me | Theorems.Thm_GlobalTheory_UnRep_ReflGen_herm_span
-- name    : GlobalTheory.UnRep.ReflGen.herm_span
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T21:23:11.545374+00:00
-- url     : https://prove2.me/theorems/441d6c23-45cc-4e3e-acdd-e2ee893952f9
-- title:
--   Refl Gen: herm span
-- statement:
--   The Refl Gen construction uses the herm span property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/UnitaryMatrixEqProdQuasiReflections.lean#L69-L78
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/UnitaryMatrixEqProdQuasiReflections.lean#L69-L78

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
omit [NumberField F] [NumberField E]

theorem GlobalTheory.UnRep.ReflGen.herm_span {v x z y : Fin n → E} (hx : hermE c G v x = 0) (hz : hermE c G v z = 0)
    (hy : y ∈ Submodule.span E {x, z}) : hermE c G v y = 0 := by sorry
