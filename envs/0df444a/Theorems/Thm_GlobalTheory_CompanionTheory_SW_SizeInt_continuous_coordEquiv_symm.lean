-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SW_SizeInt_continuous_coordEquiv_symm
-- name    : GlobalTheory.CompanionTheory.SW.SizeInt.continuous_coordEquiv_symm
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T12:09:20.800519+00:00
-- url     : https://prove2.me/theorems/d8ac634d-785f-45cd-b038-53a66536ffa0
-- title:
--   Size Int: continuous coord Equiv symm
-- statement:
--   The Size Int construction uses the continuous coord Equiv symm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/SizeFunctionRapidDecayIntegrable.lean#L98-L114
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/SizeFunctionRapidDecayIntegrable.lean#L98-L114

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_IsEulerProd
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_TensorLocallyCompactRingStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_SizeFunctionRapidDecayIntegrable
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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.SizeInt
variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]
variable {d : ℕ} (hF : IsTotallyReal F) (b : Module.Basis (Fin d) F E)

theorem GlobalTheory.CompanionTheory.SW.SizeInt.continuous_coordEquiv_symm
    (hc : IsHomeomorph fun (y : Ainf F ⊗[F] E) (k : Fin d) =>
      (Algebra.TensorProduct.basis (Ainf F) b).repr y k) :
    Continuous (coordEquiv hF b).symm := by sorry
