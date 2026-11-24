-- Prove2me | Theorems.Thm_GlobalTheory_LocalQuad_isotropic_four
-- name    : GlobalTheory.LocalQuad.isotropic_four
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T18:16:59.249185+00:00
-- url     : https://prove2.me/theorems/afd23ed0-53b4-4d14-9e05-3a7ea7d9a1e2
-- title:
--   Local Quad: isotropic four
-- statement:
--   The Local Quad construction uses the isotropic four property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/ExistsCongrIffTraceFormsIsometricCm.lean#L94-L131
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/ExistsCongrIffTraceFormsIsometricCm.lean#L94-L131

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

theorem GlobalTheory.LocalQuad.isotropic_four (H : GlobalTheory.Published.HasseNormSt) (F : Type) [Field F] [NumberField F]
    (a : Fin 4 → F) (ha : ∀ i, a i ≠ 0)
    (hr : ∀ σ : F →+* ℝ, ∃ x : Fin 4 → ℝ, x ≠ 0 ∧ ∑ i, σ (a i) * x i ^ 2 = 0)
    (hf : ∀ v : HeightOneSpectrum (𝓞 F), ∃ x : Fin 4 → v.adicCompletion F, x ≠ 0 ∧
      ∑ i, algebraMap F (v.adicCompletion F) (a i) * x i ^ 2 = 0) :
    ∃ x : Fin 4 → F, x ≠ 0 ∧ ∑ i, a i * x i ^ 2 = 0 := by sorry
