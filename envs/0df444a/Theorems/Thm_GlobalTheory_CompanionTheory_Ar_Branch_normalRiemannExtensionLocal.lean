-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Ar_Branch_normalRiemannExtensionLocal
-- name    : GlobalTheory.CompanionTheory.Ar.Branch.normalRiemannExtensionLocal
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T11:59:17.976106+00:00
-- url     : https://prove2.me/theorems/88463d4c-27fe-4f33-9b75-fc5801bd2282
-- title:
--   Branch: normal Riemann Extension Local
-- statement:
--   The Branch construction uses the normal Riemann Extension Local property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/NormalRiemannExtensionLocal.lean#L14-L86
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/NormalRiemannExtensionLocal.lean#L14-L86

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StNormalRiemannExtensionLocal
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StLocalUniversalDenominator
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StNormalBoundedQuotient
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PNormalLocallyIrreducible
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StIrreducibleGermCurve
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StCentredDiscCoverCurve
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_NormalRiemannExtensionLocal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Branch
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets MvPolynomial Topology Filter Metric

theorem GlobalTheory.CompanionTheory.Ar.Branch.normalRiemannExtensionLocal (hud : LocalUniversalDenominator.Statement)
    (hbq : NormalBoundedQuotient.Statement) (hvan : VanishNearPoint.Statement) :
    NormalRiemannExtensionLocal.Statement := by sorry
