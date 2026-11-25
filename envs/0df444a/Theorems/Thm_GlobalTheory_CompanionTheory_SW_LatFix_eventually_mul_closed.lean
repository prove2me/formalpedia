-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SW_LatFix_eventually_mul_closed
-- name    : GlobalTheory.CompanionTheory.SW.LatFix.eventually_mul_closed
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T12:02:31.034227+00:00
-- url     : https://prove2.me/theorems/8b9b7456-9861-4a01-ba4c-bed26d9cf5c2
-- title:
--   Lat Fix: eventually mul closed
-- statement:
--   The Lat Fix construction uses the eventually mul closed property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/EventuallyActMemLatVIff.lean#L42-L55
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/EventuallyActMemLatVIff.lean#L42-L55

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_BinaryMassMeans_MeanVal
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_AdelicTupleProjections
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_EventuallyActMemLatVIff
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PositivityTheory.Rg.Mass HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology Filter
open scoped TensorProduct ENNReal NNReal
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.LatFix
variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]

theorem GlobalTheory.CompanionTheory.SW.LatFix.eventually_mul_closed {d : ℕ} (b : Module.Basis (Fin d) F E) :
    ∀ᶠ v : HeightOneSpectrum (𝓞 F) in cofinite, ∀ x y : Fv F v ⊗[F] E,
      (∀ k, (Algebra.TensorProduct.basis (Fv F v) b).repr x k ∈ v.adicCompletionIntegers F) →
      (∀ k, (Algebra.TensorProduct.basis (Fv F v) b).repr y k ∈ v.adicCompletionIntegers F) →
      ∀ k, (Algebra.TensorProduct.basis (Fv F v) b).repr (x * y) k ∈
        v.adicCompletionIntegers F := by sorry
