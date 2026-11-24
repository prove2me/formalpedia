-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_TfLoc_Iw_sigma_mem_iff
-- name    : GlobalTheory.CompanionTheory.TfLoc.Iw.sigma_mem_iff
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T12:16:35.956051+00:00
-- url     : https://prove2.me/theorems/9fed903e-bda3-4cbc-8b5a-cf31950b926f
-- title:
--   Iw: sigma mem iff
-- statement:
--   The Iw construction uses the sigma mem iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/IwahoriFactorization.lean#L284-L293
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/IwahoriFactorization.lean#L284-L293

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_TwistedFactors_IntegralUnitBaseChange_Development
import Definitions.Def_GroundTheory_LocalFields_Integers
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_IwahoriFactorization
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ValuativeRel PositivityTheory.Rg.Tf.Loc Matrix
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.TfLoc GlobalTheory.CompanionTheory.TfLoc.Iw
variable {k E : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
  [Algebra k E] [ValuativeExtension k E] [FiniteDimensional k E]

theorem GlobalTheory.CompanionTheory.TfLoc.Iw.sigma_mem_iff [IsGalois k E] {n : ℕ} (τ : E ≃ₐ[k] E) (g : GL (Fin n) E) :
    sigmaGL τ g ∈ iwahori (m := n) E ↔ g ∈ iwahori (m := n) E := by sorry
