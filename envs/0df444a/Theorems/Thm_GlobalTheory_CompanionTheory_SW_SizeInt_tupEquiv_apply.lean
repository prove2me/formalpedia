-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SW_SizeInt_tupEquiv_apply
-- name    : GlobalTheory.CompanionTheory.SW.SizeInt.tupEquiv_apply
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T12:10:54.226542+00:00
-- url     : https://prove2.me/theorems/a5d9a47c-8991-4f16-87ef-154a6d361e00
-- title:
--   Size Int: tup Equiv apply
-- statement:
--   The Size Int construction uses the tup Equiv apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/SizeFunctionRapidDecayIntegrable.lean#L66-L67
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/SizeFunctionRapidDecayIntegrable.lean#L66-L67

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

theorem GlobalTheory.CompanionTheory.SW.SizeInt.tupEquiv_apply (n M : ℕ) (X : Fin n → Fin M → Ainf F ⊗[F] E) (a : Fin n) (i : Fin M) :
    tupEquiv hF b n M X a i = coordEquiv hF b (X a i) := by sorry
