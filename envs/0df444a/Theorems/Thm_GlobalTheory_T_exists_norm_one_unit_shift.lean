-- Prove2me | Theorems.Thm_GlobalTheory_T_exists_norm_one_unit_shift
-- name    : GlobalTheory.T.exists_norm_one_unit_shift
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:48:16.805082+00:00
-- url     : https://prove2.me/theorems/3a5cad3a-dc4d-45f8-9b1d-aeaca67aab0f
-- title:
--   T: exists norm one unit shift
-- statement:
--   The T construction uses the exists norm one unit shift property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/ExistsNormOneUnitShiftStatement.lean#L9-L10
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/ExistsNormOneUnitShiftStatement.lean#L9-L10

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_ExistsNormOneUnitShift
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicUnitaryOrbits_InclRAlgebraMap
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicUnitaryOrbits_StLamOf
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_IsEulerProd
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_ExistsNormOneUnitShiftStatement
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

theorem GlobalTheory.T.exists_norm_one_unit_shift : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (R : Type) [CommRing R] [Algebra F R], PIW.AdelicOrbitU.UnitChoice R → ∀ (t : R ⊗[F] E) (β : Rˣ), ∃ lam : R ⊗[F] E, lam * sigR R σ lam = 1 ∧ IsUnit (algebraMap R (R ⊗[F] E) (β : R) - sigR R σ lam * t) := by sorry
