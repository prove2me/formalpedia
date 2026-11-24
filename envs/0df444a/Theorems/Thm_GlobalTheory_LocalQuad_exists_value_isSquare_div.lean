-- Prove2me | Theorems.Thm_GlobalTheory_LocalQuad_exists_value_isSquare_div
-- name    : GlobalTheory.LocalQuad.exists_value_isSquare_div
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T18:14:11.182383+00:00
-- url     : https://prove2.me/theorems/7f9785a7-79c7-4ef2-8a7a-9393bd002a3f
-- title:
--   Local Quad: exists value is Square div
-- statement:
--   The Local Quad construction uses the exists value is Square div property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/ExistsCongrIffTraceFormsIsometricCm.lean#L137-L199
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/ExistsCongrIffTraceFormsIsometricCm.lean#L137-L199

import Mathlib
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_AdelicLattices__AlgebraMapNormOfBasisOneSqrt_07cf76d090f2548e
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Landherr__ExistsNormTensor_9eff20d6b37353d0
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsQuaternaryOfCoordinates
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_IsSquareOfValuedSubOneLt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsUnitValuedTernaryLtOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsZeroFiveOfValuation
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsForallAbvSubLt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsRingHomAdicCompletion
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsZeroCoordNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsCongrIffTraceFormsIsometric
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsCongrIffTraceFormsIsometricCm
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain
open scoped Matrix WithZero
open GlobalTheory GlobalTheory.LocalQuad

theorem GlobalTheory.LocalQuad.exists_value_isSquare_div (F : Type) [Field F] [NumberField F] {a a' : F} (ha : a ≠ 0)
    (T : Finset (HeightOneSpectrum (𝓞 F))) (p q : (v : T) → v.1.adicCompletion F)
    (hpq : ∀ v, algebraMap F _ a * p v ^ 2 + algebraMap F _ a' * q v ^ 2 ≠ 0)
    (p' q' : (F →+* ℝ) → ℝ) (hpq' : ∀ σ, σ a * p' σ ^ 2 + σ a' * q' σ ^ 2 ≠ 0) :
    ∃ x y : F, a * x ^ 2 + a' * y ^ 2 ≠ 0 ∧
      (∀ v : T, IsSquare (algebraMap F (v.1.adicCompletion F) (a * x ^ 2 + a' * y ^ 2) /
        (algebraMap F _ a * p v ^ 2 + algebraMap F _ a' * q v ^ 2))) ∧
      ∀ σ : F →+* ℝ, IsSquare (σ (a * x ^ 2 + a' * y ^ 2) / (σ a * p' σ ^ 2 + σ a' * q' σ ^ 2)) := by sorry
