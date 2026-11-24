-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SW_Glue_exists_glue
-- name    : GlobalTheory.CompanionTheory.SW.Glue.exists_glue
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T12:05:06.501108+00:00
-- url     : https://prove2.me/theorems/afb5a602-8728-46cf-99d9-a6b086ac8e26
-- title:
--   Glue: exists glue
-- statement:
--   The Glue construction uses the exists glue property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/AdelicTupleLocalGlobalProperties.lean#L112-L131
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/AdelicTupleLocalGlobalProperties.lean#L112-L131

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_HypJ
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_AdelicTupleLocalGlobalProperties
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix RestrictedProduct
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.Glue
variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]
variable {d M n : ℕ} (b : Module.Basis (Fin d) F E)

theorem GlobalTheory.CompanionTheory.SW.Glue.exists_glue (Xinf : Fin n → Fin M → Ainf F ⊗[F] E)
    (Xv : ∀ v : HeightOneSpectrum (𝓞 F), Fin n → Fin M → Fv F v ⊗[F] E)
    (h : ∀ᶠ v in Filter.cofinite, Xv v ∈ latV b v) :
    ∃ X : Fin n → Fin M → AF F ⊗[F] E, projInf X = Xinf ∧ ∀ v, projV v (projFin X) = Xv v := by sorry
