-- Prove2me | Theorems.Thm_GlobalTheory_LocalQuad_isotropic_ternary_of_units
-- name    : GlobalTheory.LocalQuad.isotropic_ternary_of_units
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T18:19:08.482838+00:00
-- url     : https://prove2.me/theorems/25bf56b2-59f9-48cd-bcc8-22db3e7d5853
-- title:
--   Local Quad: isotropic ternary of units
-- statement:
--   The Local Quad construction uses the isotropic ternary of units property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/ExistsCongrIffTraceFormsIsometricCm.lean#L18-L56
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/ExistsCongrIffTraceFormsIsometricCm.lean#L18-L56

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

theorem GlobalTheory.LocalQuad.isotropic_ternary_of_units (F : Type) [Field F] [NumberField F]
    (v : HeightOneSpectrum (𝓞 F)) (h2 : Valued.v (2 : v.adicCompletion F) = 1)
    (a : Fin 3 → v.adicCompletion F) (ha : ∀ i, Valued.v (a i) = 1) :
    ∃ x : Fin 3 → v.adicCompletion F, x ≠ 0 ∧ ∑ i, a i * x i ^ 2 = 0 := by sorry
