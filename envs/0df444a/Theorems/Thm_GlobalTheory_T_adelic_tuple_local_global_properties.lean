-- Prove2me | Theorems.Thm_GlobalTheory_T_adelic_tuple_local_global_properties
-- name    : GlobalTheory.T.adelic_tuple_local_global_properties
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T20:26:27.621435+00:00
-- url     : https://prove2.me/theorems/ce74f3d1-3c98-476b-b2a7-175a6ea39e38
-- title:
--   T: adelic tuple local global properties
-- statement:
--   The T construction uses the adelic tuple local global properties property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/AdelicTupleLocalGlobalPropertiesStatement.lean#L7-L8
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/AdelicTupleLocalGlobalPropertiesStatement.lean#L7-L8

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_AdelicTupleLocalGlobalProperties
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_HypJ
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_AdelicTupleLocalGlobalPropertiesStatement
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
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.adelic_tuple_local_global_properties : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (n M : ℕ), (∀ X Y : Fin n → Fin M → AF F ⊗[F] E, projInf X = projInf Y → (∀ v, projV v (projFin X) = projV v (projFin Y)) → X = Y) ∧ (∀ X : Fin n → Fin M → AF F ⊗[F] E, ∀ᶠ v in Filter.cofinite, projV v (projFin X) ∈ latV b v) ∧ (∀ (Xinf : Fin n → Fin M → Ainf F ⊗[F] E) (Xv : ∀ v : HeightOneSpectrum (𝓞 F), Fin n → Fin M → Fv F v ⊗[F] E), (∀ᶠ v in Filter.cofinite, Xv v ∈ latV b v) → ∃ X : Fin n → Fin M → AF F ⊗[F] E, projInf X = Xinf ∧ ∀ v, projV v (projFin X) = Xv v) ∧ ∀ (Cinf : Set (Fin n → Fin M → Ainf F ⊗[F] E)) (Cv : ∀ v : HeightOneSpectrum (𝓞 F), Set (Fin n → Fin M → Fv F v ⊗[F] E)), IsCompact Cinf → (∀ v, IsCompact (Cv v)) → (∀ᶠ v in Filter.cofinite, Cv v ⊆ latV b v) → IsCompact {X : Fin n → Fin M → AF F ⊗[F] E | projInf X ∈ Cinf ∧ ∀ v, projV v (projFin X) ∈ Cv v} := by sorry
