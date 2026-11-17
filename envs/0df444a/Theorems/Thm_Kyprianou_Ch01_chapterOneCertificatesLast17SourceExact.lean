-- Prove2me | Theorems.Thm_Kyprianou_Ch01_chapterOneCertificatesLast17SourceExact
-- name    : Kyprianou.Ch01.chapterOneCertificatesLast17SourceExact
-- status  : Open
-- author  : @WillR
-- created : 2026-11-16T20:05:42.080052+00:00
-- url     : https://prove2.me/theorems/d330c60f-73f6-4d78-bb09-1b02a7b4ad2d
-- title:
--   Exact Chapter 1 root certificate subgroup last17
-- statement:
--   The original source-exact conjunction of 17 successive Chapter 1 milestone certificates, preserving every hypothesis and quantifier in the existing all-67 source-bound definition. This is an intermediate proof dependency required to close the final 34-certificate group in two smaller compile units. Each conjunct is independently provable as the published milestone theorem; the historical exponent sign bridge uses its already-Proved collision-safe version.
-- source:
--   Kyprianou (2006), Chapter 1, printed pp. 1–32 and Exercises 1.1–1.11; original source-exact all-67 certificate bundle and cumulative root UUID 58044726-5b53-436c-a7ca-5742308e1efe.

import Definitions.Def_Kyprianou_Ch01_All67CertificatesTargetedV3
set_option maxRecDepth 4000
open Kyprianou.Ch01
set_option autoImplicit false
universe u v

theorem Kyprianou.Ch01.chapterOneCertificatesLast17SourceExact :
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
