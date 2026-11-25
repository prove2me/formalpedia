-- Prove2me | Theorems.Thm_GlobalTheory_LocalQuad_trace_forms_and_landherr
-- name    : GlobalTheory.LocalQuad.trace_forms_and_landherr
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T12:14:28.640187+00:00
-- url     : https://prove2.me/theorems/7db94c75-f6c0-44ab-8482-377d4b651126
-- title:
--   Local Quad: trace forms and landherr
-- statement:
--   The Local Quad construction uses the trace forms and landherr property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/ExistsCongrIffTraceFormsIsometricCm.lean#L305-L323
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/ExistsCongrIffTraceFormsIsometricCm.lean#L305-L323

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
import Theorems.Thm_GlobalTheory_LocalQuad_HermClass_Congr_det

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
universe u v w in

theorem GlobalTheory.LocalQuad.trace_forms_and_landherr :
    (∀ {F : Type u} {E : Type v} [Field F] [Field E] [Algebra F E], (2 : E) ≠ 0 →
      ∀ c : E →+* E, (∀ t, c (c t) = t) → (∀ t : E, c t = t ↔ ∃ s : F, algebraMap F E s = t) →
      ∀ {n : Type w} [Fintype n] [DecidableEq n] {G G' : Matrix n n E},
      (∀ a b, c (G a b) = G b a) → (∀ a b, c (G' a b) = G' b a) → G.det ≠ 0 → G'.det ≠ 0 →
      ((∃ P : Matrix n n E, P.det ≠ 0 ∧ G' = Pᵀ * G * P.map c) ↔
        ∃ φ : (n → E) ≃ₗ[F] (n → E),
          ∀ x, x ⬝ᵥ G' *ᵥ (c ∘ x) = φ x ⬝ᵥ G *ᵥ (c ∘ φ x))) ∧
    (GlobalTheory.Published.HasseNormSt → ∀ (F : Type) [Field F] [NumberField F] {ι : Type w} [Fintype ι],
      4 ≤ Fintype.card ι → ∀ a : ι → F, (∀ i, a i ≠ 0) →
      (∀ σ : F →+* ℝ, ∃ x : ι → ℝ, x ≠ 0 ∧ ∑ i, σ (a i) * x i ^ 2 = 0) →
      (∀ v : HeightOneSpectrum (𝓞 F), ∃ x : ι → v.adicCompletion F, x ≠ 0 ∧
        ∑ i, algebraMap F (v.adicCompletion F) (a i) * x i ^ 2 = 0) →
      ∃ x : ι → F, x ≠ 0 ∧ ∑ i, a i * x i ^ 2 = 0) ∧
    (GlobalTheory.Published.HasseNormSt → GlobalTheory.Published.Landherr) := by sorry
