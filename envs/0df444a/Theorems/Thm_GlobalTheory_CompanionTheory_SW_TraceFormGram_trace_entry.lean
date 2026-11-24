-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SW_TraceFormGram_trace_entry
-- name    : GlobalTheory.CompanionTheory.SW.TraceFormGram.trace_entry
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T12:11:18.721765+00:00
-- url     : https://prove2.me/theorems/6f8cd6db-0c52-46ba-8002-348fd1b7eda3
-- title:
--   Trace Form Gram: trace entry
-- statement:
--   The Trace Form Gram construction uses the trace entry property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/EtaleAwayQuotientEqLocalization.lean#L34-L49
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/EtaleAwayQuotientEqLocalization.lean#L34-L49

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_IsEulerProd
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_EtaleAwayQuotientEqLocalization
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.TraceFormGram
open HeckeCharacterZeroLocus.SiegelWeilU
open scoped TensorProduct Matrix
variable {F E : Type} [Field F] [Field E] [Algebra F E]

theorem GlobalTheory.CompanionTheory.SW.TraceFormGram.trace_entry [FiniteDimensional F E] (σ : E →ₐ[F] E) {d : ℕ} (b : Module.Basis (Fin d) F E)
    (R : Type) [CommRing R] [Algebra F R] (u v : R ⊗[F] E) (e : E) :
    Algebra.trace R (R ⊗[F] E) (sigR R σ u * ((1 : R) ⊗ₜ[F] e) * v) =
      ∑ k, ∑ l, (Algebra.TensorProduct.basis R b).repr u k *
        (algebraMap F R (Algebra.trace F E (σ (b k) * e * b l)) *
          (Algebra.TensorProduct.basis R b).repr v l) := by sorry
