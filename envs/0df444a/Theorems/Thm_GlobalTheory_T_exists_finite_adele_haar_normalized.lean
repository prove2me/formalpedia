-- Prove2me | Theorems.Thm_GlobalTheory_T_exists_finite_adele_haar_normalized
-- name    : GlobalTheory.T.exists_finite_adele_haar_normalized
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T12:33:28.291107+00:00
-- url     : https://prove2.me/theorems/dfd3bcc1-0b2d-5283-bf99-5373ed406a5f
-- title:
--   T: exists finite adele haar normalized
-- statement:
--   The T construction uses the exists finite adele haar normalized property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/ExistsFiniteAdeleHaarNormalizedStatement.lean#L7-L8
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/ExistsFiniteAdeleHaarNormalizedStatement.lean#L7-L8

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_ExistsFiniteAdeleHaarNormalized
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_GaussQ
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_ExistsFiniteAdeleHaarNormalizedStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.BB NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.exists_finite_adele_haar_normalized : ∀ (F : Type) [Field F] [NumberField F], ∃ lf : Measure (Af F), lf.IsAddHaarMeasure ∧ lf {x | ∀ v, x v ∈ v.adicCompletionIntegers F} = 1 := by sorry
