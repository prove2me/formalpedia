-- Prove2me | Theorems.Thm_Kyprianou_Ch01_chapterOneCertificatesMiddle17SourceExact
-- name    : Kyprianou.Ch01.chapterOneCertificatesMiddle17SourceExact
-- status  : Open
-- author  : @WillR
-- created : 2026-11-16T20:05:23.24257+00:00
-- url     : https://prove2.me/theorems/aeb020a5-4507-4eb4-9533-b443ff4db2ad
-- title:
--   Exact Chapter 1 root certificate subgroup middle17
-- statement:
--   The original source-exact conjunction of 17 successive Chapter 1 milestone certificates, preserving every hypothesis and quantifier in the existing all-67 source-bound definition. This is an intermediate proof dependency required to close the final 34-certificate group in two smaller compile units. Each conjunct is independently provable as the published milestone theorem; the historical exponent sign bridge uses its already-Proved collision-safe version.
-- source:
--   Kyprianou (2006), Chapter 1, printed pp. 1–32 and Exercises 1.1–1.11; original source-exact all-67 certificate bundle and cumulative root UUID 58044726-5b53-436c-a7ca-5742308e1efe.

import Definitions.Def_Kyprianou_Ch01_All67CertificatesTargetedV3
set_option maxRecDepth 4000
open Kyprianou.Ch01
set_option autoImplicit false
universe u v

theorem Kyprianou.Ch01.chapterOneCertificatesMiddle17SourceExact :
    certificate_lampertiBranchingToCompoundPoissonPathLawWithoutMoment.{u,v} ∧
    certificate_generalFrullaniImproper ∧ certificate_stableAlphaOneCosineIntegral ∧
    certificate_stableAlphaAboveOneIntegral ∧ certificate_inverseGaussianDensityLaplace ∧
    certificate_brownianDiscountedLowerPassage.{u} ∧
    certificate_queueLaplaceExponentStrictConvexAndRoot ∧
    certificate_queueExponentialMartingaleAndPassage.{u} ∧
    certificate_mckeanBarrierCalculusOptimality ∧ certificate_stableAlphaOneLogPhase ∧
    certificate_inverseGaussianLevyExponent ∧
    certificate_firstWeakDescendingRenewalPotential.{u} ∧
    certificate_riskEmbeddedRandomWalkTails ∧ certificate_exponentialAscendingLadderRenewal ∧
    certificate_brownianPassageHalfStableLevyProcess.{u} ∧
    certificate_stableLevyExponentFormAwayFromOne ∧ certificate_stableLevyExponentFormIndexOne := by
  sorry
