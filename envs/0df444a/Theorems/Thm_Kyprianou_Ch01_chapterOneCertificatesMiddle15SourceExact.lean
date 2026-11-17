-- Prove2me | Theorems.Thm_Kyprianou_Ch01_chapterOneCertificatesMiddle15SourceExact
-- name    : Kyprianou.Ch01.chapterOneCertificatesMiddle15SourceExact
-- status  : Open
-- author  : @WillR
-- created : 2026-11-16T20:09:47.464346+00:00
-- url     : https://prove2.me/theorems/2a18b9a6-e0d8-4a57-8203-6e688c98beb6
-- title:
--   Exact source-bound middle 15 Chapter 1 certificate conjunction
-- statement:
--   The original fifteen Chapter 1 source-bound certificate statements numbered 34 through 48 in their original conjunction order. All mathematical hypotheses, quantifiers and cases are unchanged. This compiler-verified subdivision separates two historical exponent-module import conflicts from the other fifteen obligations. Each conjunct is proved or reduced by importing its existing published theorem statement.
-- source:
--   Kyprianou (2006), Chapter 1, all source-bound milestones and exercises; the original all-67 certificate Definition and root UUID 58044726-5b53-436c-a7ca-5742308e1efe.

import Definitions.Def_Kyprianou_Ch01_All67CertificatesTargetedV3
set_option maxRecDepth 4000
open Kyprianou.Ch01
set_option autoImplicit false
universe u v

theorem Kyprianou.Ch01.chapterOneCertificatesMiddle15SourceExact :
    certificate_lampertiBranchingToCompoundPoissonPathLawWithoutMoment.{u,v} ∧
    certificate_generalFrullaniImproper ∧ certificate_stableAlphaOneCosineIntegral ∧
    certificate_stableAlphaAboveOneIntegral ∧ certificate_inverseGaussianDensityLaplace ∧
    certificate_brownianDiscountedLowerPassage.{u} ∧
    certificate_queueLaplaceExponentStrictConvexAndRoot ∧
    certificate_queueExponentialMartingaleAndPassage.{u} ∧
    certificate_mckeanBarrierCalculusOptimality ∧ certificate_stableAlphaOneLogPhase ∧
    certificate_inverseGaussianLevyExponent ∧
    certificate_firstWeakDescendingRenewalPotential.{u} ∧
    certificate_riskEmbeddedRandomWalkTails ∧
    certificate_exponentialAscendingLadderRenewal ∧
    certificate_brownianPassageHalfStableLevyProcess.{u} := by
  sorry
