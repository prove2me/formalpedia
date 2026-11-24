-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SW_SizeInt_norm_tupEquiv_le
-- name    : GlobalTheory.CompanionTheory.SW.SizeInt.norm_tupEquiv_le
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T12:09:27.219798+00:00
-- url     : https://prove2.me/theorems/ffc20093-d534-4884-bea3-c2d8dbd0b81b
-- title:
--   Size Int: norm tup Equiv le
-- statement:
--   The Size Int construction uses the norm tup Equiv le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/SizeFunctionRapidDecayIntegrable.lean#L69-L90
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/SizeFunctionRapidDecayIntegrable.lean#L69-L90

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

theorem GlobalTheory.CompanionTheory.SW.SizeInt.norm_tupEquiv_le (n M : ℕ) (X : Fin n → Fin M → Ainf F ⊗[F] E) :
    ‖tupEquiv hF b n M X‖ ≤ sizeTup b X := by sorry
