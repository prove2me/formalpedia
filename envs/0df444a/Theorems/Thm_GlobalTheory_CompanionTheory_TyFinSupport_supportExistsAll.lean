-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_TyFinSupport_supportExistsAll
-- name    : GlobalTheory.CompanionTheory.TyFinSupport.supportExistsAll
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T19:24:18.589971+00:00
-- url     : https://prove2.me/theorems/d50f7730-cfa4-42c7-be3d-51874ff478b4
-- title:
--   Ty Fin Support: support Exists All
-- statement:
--   The Ty Fin Support construction uses the support Exists All property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/CuspidalSupportExists.lean#L64-L69
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/CuspidalSupportExists.lean#L64-L69

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_FiniteTypeHarishChandra_SupportExistsAll
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IrreducibleCharacterSeries_FrobeniusSumFormula
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_JacquetModuleAll
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CuspidalSupportExists
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Formalism.IrreducibleCountingLemmas.TYPES
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.TyFinSupport

theorem GlobalTheory.CompanionTheory.TyFinSupport.supportExistsAll : ReciprocityTheory.Ty.Fin.St.SupportExistsAll := by sorry
