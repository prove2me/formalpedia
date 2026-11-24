-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SW_MeasProj_exists_glue
-- name    : GlobalTheory.CompanionTheory.SW.MeasProj.exists_glue
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T12:07:58.517799+00:00
-- url     : https://prove2.me/theorems/554a97a6-0808-47cb-974a-bcac7fb45679
-- title:
--   Meas Proj: exists glue
-- statement:
--   The Meas Proj construction uses the exists glue property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/AdelicTupleProjections.lean#L161-L185
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/AdelicTupleProjections.lean#L161-L185

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_IsEulerProd
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_TensorLocallyCompactRing
import Definitions.Def_GroundTheory_GlobalFields_LocalAtPlace
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_AdelicTupleProjections
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.MeasProj
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]

theorem GlobalTheory.CompanionTheory.SW.MeasProj.exists_glue {d n M : ℕ} (b : Module.Basis (Fin d) F E) (Y : Fin n → Fin M → Ainf F ⊗[F] E)
    (Z : ∀ v : HeightOneSpectrum (𝓞 F), (Fin n → Fin M → Fv F v ⊗[F] E))
    (hZ : ∀ᶠ v in Filter.cofinite, Z v ∈ (latV b v : Set (Fin n → Fin M → Fv F v ⊗[F] E))) :
    ∃ X : (Fin n → Fin M → AF F ⊗[F] E), projInf X = Y ∧ ∀ v, projV v (projFin X) = Z v := by sorry
