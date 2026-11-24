-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SW_PrimGood_change_basis
-- name    : GlobalTheory.CompanionTheory.SW.PrimGood.change_basis
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T12:08:33.072548+00:00
-- url     : https://prove2.me/theorems/fe491609-7458-4298-9ed1-89c3605eed9b
-- title:
--   Prim Good: change basis
-- statement:
--   The Prim Good construction uses the change basis property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/PrimitiveVectorLatticeRescaleAlmostAll.lean#L419-L438
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/PrimitiveVectorLatticeRescaleAlmostAll.lean#L419-L438

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_HypJ
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_IntegralAlmostAllPlaces
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_IsSquareOfValuedSubOneLt
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_PrimitiveVectorLatticeRescaleAlmostAll
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.PrimGood
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem GlobalTheory.CompanionTheory.SW.PrimGood.change_basis {d d' : ℕ} (b : Module.Basis (Fin d) F E) (b' : Module.Basis (Fin d') F E) :
    ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, ∀ x : Fv F v ⊗[F] E,
      (∀ k, (Algebra.TensorProduct.basis (Fv F v) b).repr x k ∈ v.adicCompletionIntegers F) →
      ∀ k, (Algebra.TensorProduct.basis (Fv F v) b').repr x k ∈ v.adicCompletionIntegers F := by sorry
