-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SW_StabFirst_blockOne_mulVec_cons
-- name    : GlobalTheory.CompanionTheory.SW.StabFirst.blockOne_mulVec_cons
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T12:09:51.791745+00:00
-- url     : https://prove2.me/theorems/9f3481c3-cc2d-4c9a-9917-bce784a7d96a
-- title:
--   Stab First: block One mul Vec cons
-- statement:
--   The Stab First construction uses the block One mul Vec cons property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/BlockOneRightInjective.lean#L144-L148
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/BlockOneRightInjective.lean#L144-L148

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_IsEulerProd
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_BlockOneRightInjective
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.StabFirst
variable {K : Type} [CommRing K] {M : ℕ}

theorem GlobalTheory.CompanionTheory.SW.StabFirst.blockOne_mulVec_cons (A : Matrix (Fin M) (Fin M) K) (x : Fin M → K) :
    (blockOne 1 A).mulVec (Fin.cons 0 x) = Fin.cons 0 (A.mulVec x) := by sorry
