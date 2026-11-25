-- Prove2me | Theorems.Thm_GlobalTheory_T_unitary_action_cons_tuple_measurable
-- name    : GlobalTheory.T.unitary_action_cons_tuple_measurable
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T12:40:44.254716+00:00
-- url     : https://prove2.me/theorems/768c6f94-696d-4f51-881b-8eeda74f0085
-- title:
--   T: unitary action cons tuple measurable
-- statement:
--   The T construction uses the unitary action cons tuple measurable property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/UnitaryActionConsTupleMeasurableStatement.lean#L7-L8
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/UnitaryActionConsTupleMeasurableStatement.lean#L7-L8

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_UnitaryActionConsTupleMeasurable
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_IsEulerProd
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_UnitaryActionConsTupleMeasurableStatement
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

theorem GlobalTheory.T.unitary_action_cons_tuple_measurable : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [MeasurableSpace R] [BorelSpace R], IsLocR R → ∀ (n M : ℕ) (J : Matrix (Fin (M + 1)) (Fin (M + 1)) E) (g : HA R σ J), Measurable (fun X : Fin n → Fin M → R ⊗[F] E => actW R σ J g (consTup X)) := by sorry
