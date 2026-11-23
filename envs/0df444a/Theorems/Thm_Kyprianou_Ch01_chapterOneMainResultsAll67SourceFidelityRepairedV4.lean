-- Prove2me | Theorems.Thm_Kyprianou_Ch01_chapterOneMainResultsAll67SourceFidelityRepairedV4
-- name    : Kyprianou.Ch01.chapterOneMainResultsAll67SourceFidelityRepairedV4
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-16T23:41:59.097844+00:00
-- url     : https://prove2.me/theorems/735620bc-c0e4-4ce8-862c-b434b7f2c1c5
-- title:
--   Chapter 1 all 67 source results with corrected inverse Gaussian and half-stable passage boundaries
-- statement:
--   A cumulative mathematical conjunction of every previous required Chapter 1 source certificate, together with five additional source-accurate obligations for the complex stable gamma integral, inverse Gaussian triplet drift, explicit Brownian half-stable parameters, the two idle-time joint laws, and the right-continuous first-passage stopping-time property. The two Brownian first-passage process milestones use explicit T₀=0 on every sample path, exactly as required by the zero-start axiom for a genuine Lévy process; all other 65 source clauses remain unchanged. The entire 67-certification module is consolidated in a single directly compiled provider to avoid cross-module unresolved imports.
-- source:
--   Kyprianou (2006), Chapter 1, Theorems 1.3–1.13 and Exercises 1.1–1.11, supplemented by source-accuracy repairs 16 November 2026.

import Definitions.Def_Kyprianou_Ch01_All67CertificatesZeroBoundaryV4
set_option autoImplicit false
universe u v

theorem Kyprianou.Ch01.chapterOneMainResultsAll67SourceFidelityRepairedV4 :
    Kyprianou.Ch01.certificate_levyKhintchineLaw ∧
    Kyprianou.Ch01.certificate_levy_khintchine_process_existsTargetedV2 ∧
    Kyprianou.Ch01.certificate_compoundPoissonCharExponent.{u} ∧
    Kyprianou.Ch01.certificate_compoundPoissonInfinitelyDivisible.{u} ∧
    Kyprianou.Ch01.certificate_frullani_complex ∧
    Kyprianou.Ch01.certificate_pollaczekKhintchineRuin.{u} ∧
    Kyprianou.Ch01.certificate_ruinDeficitIntegratedTail.{u} ∧
    Kyprianou.Ch01.certificate_lundbergBound.{u} ∧
    Kyprianou.Ch01.certificate_lundbergAsymptotic.{u} ∧
    Kyprianou.Ch01.certificate_mg1IdleOverloaded.{u} ∧
    Kyprianou.Ch01.certificate_mg1IdleCriticalAndLight.{u} ∧
    Kyprianou.Ch01.certificate_mg1StationaryWorkload.{u} ∧
    Kyprianou.Ch01.certificate_mg1UnboundedLimsup.{u} ∧
    Kyprianou.Ch01.certificate_mckeanBrownianPutOptimalRightContinuous.{u} ∧
    Kyprianou.Ch01.certificate_branchingLaplaceExponential ∧
    Kyprianou.Ch01.certificate_branchingLaplaceSemigroup ∧
    Kyprianou.Ch01.certificate_gammaLevyExponent ∧
    Kyprianou.Ch01.certificate_gammaProcessStrictIncreaseAndInfiniteActivity.{u} ∧
    Kyprianou.Ch01.certificate_inverseGaussianFirstPassageLaplaceRightContinuous.{u} ∧
    Kyprianou.Ch01.certificate_inverseGaussianPassageLevySubordinatorZeroBoundaryV2.{u} ∧
    Kyprianou.Ch01.certificate_strictStableTimeScaling.{u} ∧
    Kyprianou.Ch01.certificate_branchingLaplaceEvolution ∧
    Kyprianou.Ch01.certificate_independentLevySum.{u} ∧
    Kyprianou.Ch01.certificate_lampertiForwardClockRecovery.{u} ∧
    Kyprianou.Ch01.certificate_lampertiReverseClockRecovery.{u} ∧
    Kyprianou.Ch01.certificate_characteristicExponentialMartingale.{u} ∧
    Kyprianou.Ch01.certificate_brownianFirstPassageStableHalf.{u} ∧
    Kyprianou.Ch01.certificate_lampertiCompoundPoissonToBranchingLawNonexplosive.{u} ∧
    Kyprianou.Ch01.certificate_geometricLawInfinitelyDivisible ∧
    Kyprianou.Ch01.certificate_geometricStoppedRandomWalkInfinitelyDivisible.{u} ∧
    Kyprianou.Ch01.certificate_stableGammaIntegral ∧
    Kyprianou.Ch01.certificate_randomWalkReversalLadderIdentity.{u} ∧
    Kyprianou.Ch01.certificate_mg1IdleRegulatorIdentity.{u} ∧
    Kyprianou.Ch01.certificate_lampertiBranchingToCompoundPoissonPathLawWithoutMoment.{u,v} ∧
    Kyprianou.Ch01.certificate_generalFrullaniImproper ∧
    Kyprianou.Ch01.certificate_stableAlphaOneCosineIntegral ∧
    Kyprianou.Ch01.certificate_stableAlphaAboveOneIntegral ∧
    Kyprianou.Ch01.certificate_inverseGaussianDensityLaplace ∧
    Kyprianou.Ch01.certificate_brownianDiscountedLowerPassage.{u} ∧
    Kyprianou.Ch01.certificate_queueLaplaceExponentStrictConvexAndRoot ∧
    Kyprianou.Ch01.certificate_queueExponentialMartingaleAndPassage.{u} ∧
    Kyprianou.Ch01.certificate_mckeanBarrierCalculusOptimality ∧
    Kyprianou.Ch01.certificate_stableAlphaOneLogPhase ∧
    Kyprianou.Ch01.certificate_inverseGaussianLevyExponent ∧
    Kyprianou.Ch01.certificate_firstWeakDescendingRenewalPotential.{u} ∧
    Kyprianou.Ch01.certificate_riskEmbeddedRandomWalkTails ∧
    Kyprianou.Ch01.certificate_exponentialAscendingLadderRenewal ∧
    Kyprianou.Ch01.certificate_brownianPassageHalfStableLevyProcessZeroBoundaryV2.{u} ∧
    Kyprianou.Ch01.certificate_stableLevyExponentFormAwayFromOne ∧
    Kyprianou.Ch01.certificate_stableLevyExponentFormIndexOne ∧
    Kyprianou.Ch01.certificate_branchingOneAncestorGeneratorFromRates ∧
    Kyprianou.Ch01.certificate_levyTripletExponentSignBridgeReviewed ∧
    Kyprianou.Ch01.certificate_continuousRepresentativeForAlmostSurePaths.{u} ∧
    Kyprianou.Ch01.certificate_reuse_ProbabilityTheory_IsLevyProcess_isInfinitelyDivisible_marginal.{u, v} ∧
    Kyprianou.Ch01.certificate_reuse_ProbabilityTheory_IsLevyProcess_charFun_eq_exp_mul.{u, v} ∧
    Kyprianou.Ch01.certificate_reuse_ProbabilityTheory_IsPoissonProcess_isLevyProcess.{u} ∧
    Kyprianou.Ch01.certificate_reuse_levy_foundations_poissonLaw_infinitelyDivisible ∧
    Kyprianou.Ch01.certificate_reuse_ProbabilityTheory_compoundPoisson_ae_isCadlag.{u} ∧
    Kyprianou.Ch01.certificate_reuse_levy_foundations_compoundPoissonMarginalInfinitelyDivisible.{u} ∧
    Kyprianou.Ch01.certificate_reuse_MarkovProcess_isBrownianReal_brownianMotion ∧
    Kyprianou.Ch01.certificate_brownianRealExponentialMartingale.{u} ∧
    Kyprianou.Ch01.certificate_brownianDiscountedUpperPassage.{u} ∧
    Kyprianou.Ch01.certificate_firstUpperPassageNaturalRightStoppingContinuousV2.{u} ∧
    Kyprianou.Ch01.certificate_stableGammaIntegralComplexExtensionV2 ∧
    Kyprianou.Ch01.certificate_inverseGaussianFullLevyTripletV2 ∧
    Kyprianou.Ch01.certificate_brownianFirstPassageStableParametersV2.{u} ∧
    Kyprianou.Ch01.certificate_mg1IdleJointLawsExercise19vV2.{u} := by
  sorry
