-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SW_Glue_isCompact_glue
-- name    : GlobalTheory.CompanionTheory.SW.Glue.isCompact_glue
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T12:05:13.793514+00:00
-- url     : https://prove2.me/theorems/9539b902-efe2-4a2e-89e3-dfb185cf69a6
-- title:
--   Glue: is Compact glue
-- statement:
--   The Glue construction uses the is Compact glue property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/AdelicTupleLocalGlobalProperties.lean#L170-L241
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/AdelicTupleLocalGlobalProperties.lean#L170-L241

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

theorem GlobalTheory.CompanionTheory.SW.Glue.isCompact_glue (Cinf : Set (Fin n → Fin M → Ainf F ⊗[F] E))
    (Cv : ∀ v : HeightOneSpectrum (𝓞 F), Set (Fin n → Fin M → Fv F v ⊗[F] E))
    (hinf : IsCompact Cinf) (hv : ∀ v, IsCompact (Cv v))
    (hlat : ∀ᶠ v in Filter.cofinite, Cv v ⊆ latV b v) :
    IsCompact {X : Fin n → Fin M → AF F ⊗[F] E |
      projInf X ∈ Cinf ∧ ∀ v, projV v (projFin X) ∈ Cv v} := by sorry
