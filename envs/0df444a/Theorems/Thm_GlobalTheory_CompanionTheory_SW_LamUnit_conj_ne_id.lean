-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SW_LamUnit_conj_ne_id
-- name    : GlobalTheory.CompanionTheory.SW.LamUnit.conj_ne_id
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T12:06:50.146413+00:00
-- url     : https://prove2.me/theorems/f312730f-3440-4da5-8ce5-2a11bd2f9a43
-- title:
--   Lam Unit: conj ne id
-- statement:
--   The Lam Unit construction uses the conj ne id property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/ExistsNormOneUnitShift.lean#L11-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/ExistsNormOneUnitShift.lean#L11-L21

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicUnitaryOrbits_InclRAlgebraMap
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicUnitaryOrbits_StLamOf
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_IsEulerProd
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_ExistsNormOneUnitShift
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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.LamUnit

theorem GlobalTheory.CompanionTheory.SW.LamUnit.conj_ne_id {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {σ : E →ₐ[F] E} (h : IsCMExt F E σ) : σ ≠ AlgHom.id F E := by sorry
