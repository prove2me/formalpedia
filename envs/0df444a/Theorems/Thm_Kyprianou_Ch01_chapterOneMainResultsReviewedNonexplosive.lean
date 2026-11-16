-- Prove2me | Theorems.Thm_Kyprianou_Ch01_chapterOneMainResultsReviewedNonexplosive
-- name    : Kyprianou.Ch01.chapterOneMainResultsReviewedNonexplosive
-- status  : Open
-- author  : @WillR
-- created : 2026-11-15T10:21:21.043941+00:00
-- url     : https://prove2.me/theorems/7dfe3368-4903-482a-8569-ab9dab8c183a
-- title:
--   Chapter 1 reviewed source certificate with explicit non-explosion and corrected first-passage conventions
-- statement:
--   Chapter 1 certificate retaining all original source obligations with corrected McKean, corrected inverse Gaussian strict first passage, unrestricted finite-moment Lamperti scope, and explicit stable formula, branching-generator, continuity-representative and sign-convention obligations. The reverse Lamperti law now has a separate conservativity/non-explosion assumption in place of an extraneous offspring first moment.
-- source:
--   Kyprianou (2006), Chapter 1; Sousi (2011) Proposition 3.5.

import Definitions.Def_Kyprianou_Ch01_ReviewCorrectionsNonexplosive
import Definitions.Def_Kyprianou_Ch01_ReviewCorrectionsExplicitUniverse
import Definitions.Def_Kyprianou_Ch01_McKeanRightContinuousCertificate
import Definitions.Def_Kyprianou_Ch01_ChapterCertification
set_option autoImplicit false
universe u v

theorem Kyprianou.Ch01.chapterOneMainResultsReviewedNonexplosive :
    Kyprianou.Ch01.certificate_levyKhintchineLaw ∧
    Kyprianou.Ch01.certificate_levy_khintchine_process_exists ∧
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
    Kyprianou.Ch01.certificate_inverseGaussianPassageLevySubordinator.{u} ∧
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
    Kyprianou.Ch01.certificate_brownianPassageHalfStableLevyProcess.{u} ∧
    Kyprianou.Ch01.certificate_stableLevyExponentFormAwayFromOne ∧
    Kyprianou.Ch01.certificate_stableLevyExponentFormIndexOne ∧
    Kyprianou.Ch01.certificate_branchingOneAncestorGeneratorFromRates ∧
    Kyprianou.Ch01.certificate_levyTripletExponentSignBridge ∧
    Kyprianou.Ch01.certificate_continuousRepresentativeForAlmostSurePaths.{u} := by
  sorry
