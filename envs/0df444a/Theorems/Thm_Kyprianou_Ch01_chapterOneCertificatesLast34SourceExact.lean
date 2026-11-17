-- Prove2me | Theorems.Thm_Kyprianou_Ch01_chapterOneCertificatesLast34SourceExact
-- name    : Kyprianou.Ch01.chapterOneCertificatesLast34SourceExact
-- status  : Open
-- author  : @WillR
-- created : 2026-11-16T19:59:13.565432+00:00
-- url     : https://prove2.me/theorems/49a0f57c-e2c7-47f4-b8b7-693066e8b3b1
-- title:
--   Kyprianou Chapter 1 cumulative certificate conjunction, source-exact last34
-- statement:
--   An exact conjunction of 34 of the existing 67 source-bound Chapter 1 mathematical certificates, with the same original hypotheses and quantifiers and their original order. Every conjunct is the full mathematical content of its corresponding published milestone. This helper permits a compiler-compatible acyclic split of the complete chapter theorem into two conjunctions. The first theorem uses a source-equivalent already-Proved targeted exponent characterisation; the second uses a source-equivalent already-Proved targeted sign bridge.
-- source:
--   Kyprianou (2006), Chapter 1, printed pp. 1–32 and all Exercises 1.1–1.11; corresponding exact ordered source certificate Definition Kyprianou_Ch01_All67CertificatesTargetedV3; cumulative root theorem UUID 58044726-5b53-436c-a7ca-5742308e1efe.

import Definitions.Def_Kyprianou_Ch01_All67CertificatesTargetedV3
open Kyprianou.Ch01
set_option maxRecDepth 4000
set_option autoImplicit false
universe u v

theorem Kyprianou.Ch01.chapterOneCertificatesLast34SourceExact :
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
    certificate_brownianPassageHalfStableLevyProcess.{u} ∧
    certificate_stableLevyExponentFormAwayFromOne ∧
    certificate_stableLevyExponentFormIndexOne ∧
    certificate_branchingOneAncestorGeneratorFromRates ∧
    certificate_levyTripletExponentSignBridgeReviewed ∧
    certificate_continuousRepresentativeForAlmostSurePaths.{u} ∧
    certificate_reuse_ProbabilityTheory_IsLevyProcess_isInfinitelyDivisible_marginal.{u, v} ∧
    certificate_reuse_ProbabilityTheory_IsLevyProcess_charFun_eq_exp_mul.{u, v} ∧
    certificate_reuse_ProbabilityTheory_IsPoissonProcess_isLevyProcess.{u} ∧
    certificate_reuse_levy_foundations_poissonLaw_infinitelyDivisible ∧
    certificate_reuse_ProbabilityTheory_compoundPoisson_ae_isCadlag.{u} ∧
    certificate_reuse_levy_foundations_compoundPoissonMarginalInfinitelyDivisible.{u} ∧
    certificate_reuse_MarkovProcess_isBrownianReal_brownianMotion ∧
    certificate_brownianRealExponentialMartingale.{u} ∧
    certificate_brownianDiscountedUpperPassage.{u} ∧
    certificate_firstUpperPassageNaturalRightStoppingContinuousV2.{u} ∧
    certificate_stableGammaIntegralComplexExtensionV2 ∧
    certificate_inverseGaussianFullLevyTripletV2 ∧
    certificate_brownianFirstPassageStableParametersV2.{u} ∧
    certificate_mg1IdleJointLawsExercise19vV2.{u} := by
  sorry
