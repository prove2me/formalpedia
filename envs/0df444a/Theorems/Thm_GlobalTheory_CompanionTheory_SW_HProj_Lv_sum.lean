-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SW_HProj_Lv_sum
-- name    : GlobalTheory.CompanionTheory.SW.HProj.Lv_sum
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T12:05:33.581616+00:00
-- url     : https://prove2.me/theorems/08048bf6-26ab-4b12-95d2-0c77524be540
-- title:
--   HProj: Lv sum
-- statement:
--   The HProj construction uses the Lv sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/AdelicUnitaryGroupProjections.lean#L119-L123
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/AdelicUnitaryGroupProjections.lean#L119-L123

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_IsEulerProd
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_AdelicTupleProjectionsStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_AdelicUnitaryGroupProjections
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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.HProj
variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {d : ℕ}

theorem GlobalTheory.CompanionTheory.SW.HProj.Lv_sum (b : Module.Basis (Fin d) F E) (v : HeightOneSpectrum (𝓞 F)) {ι : Type} (s : Finset ι)
    (f : ι → Fv F v ⊗[F] E) (hf : ∀ i ∈ s, f i ∈ Lv b v) : ∑ i ∈ s, f i ∈ Lv b v := by sorry
