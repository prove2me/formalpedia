-- Prove2me | Theorems.Thm_Kyprianou_Ch01_chapterOneCertificatesFirst33SourceExact
-- name    : Kyprianou.Ch01.chapterOneCertificatesFirst33SourceExact
-- status  : Open
-- author  : @WillR
-- created : 2026-11-16T20:03:09.519792+00:00
-- url     : https://prove2.me/theorems/4b096503-5b44-49bf-99cc-41b5242d1b2e
-- title:
--   Kyprianou Chapter 1 cumulative certificate conjunction, source-exact first33
-- statement:
--   An exact conjunction of 33 of the existing 67 source-bound Chapter 1 mathematical certificates, with the same original hypotheses and quantifiers and their original order. Every conjunct is the full mathematical content of its corresponding published milestone. This helper permits a compiler-compatible acyclic split of the complete chapter theorem into two conjunctions. The first theorem uses a source-equivalent already-Proved targeted exponent characterisation; the second uses a source-equivalent already-Proved targeted sign bridge.
-- source:
--   Kyprianou (2006), Chapter 1, printed pp. 1–32 and all Exercises 1.1–1.11; corresponding exact ordered source certificate Definition Kyprianou_Ch01_All67CertificatesTargetedV3; cumulative root theorem UUID 58044726-5b53-436c-a7ca-5742308e1efe.

import Definitions.Def_Kyprianou_Ch01_All67CertificatesTargetedV3
open Kyprianou.Ch01
set_option maxRecDepth 4000
set_option autoImplicit false
universe u v

theorem Kyprianou.Ch01.chapterOneCertificatesFirst33SourceExact :
    certificate_levyKhintchineLaw ∧ certificate_levy_khintchine_process_existsTargetedV2 ∧
    certificate_compoundPoissonCharExponent.{u} ∧
    certificate_compoundPoissonInfinitelyDivisible.{u} ∧ certificate_frullani_complex ∧
    certificate_pollaczekKhintchineRuin.{u} ∧ certificate_ruinDeficitIntegratedTail.{u} ∧
    certificate_lundbergBound.{u} ∧ certificate_lundbergAsymptotic.{u} ∧
    certificate_mg1IdleOverloaded.{u} ∧ certificate_mg1IdleCriticalAndLight.{u} ∧
    certificate_mg1StationaryWorkload.{u} ∧ certificate_mg1UnboundedLimsup.{u} ∧
    certificate_mckeanBrownianPutOptimalRightContinuous.{u} ∧
    certificate_branchingLaplaceExponential ∧ certificate_branchingLaplaceSemigroup ∧
    certificate_gammaLevyExponent ∧
    certificate_gammaProcessStrictIncreaseAndInfiniteActivity.{u} ∧
    certificate_inverseGaussianFirstPassageLaplaceRightContinuous.{u} ∧
    certificate_inverseGaussianPassageLevySubordinator.{u} ∧
    certificate_strictStableTimeScaling.{u} ∧ certificate_branchingLaplaceEvolution ∧
    certificate_independentLevySum.{u} ∧ certificate_lampertiForwardClockRecovery.{u} ∧
    certificate_lampertiReverseClockRecovery.{u} ∧
    certificate_characteristicExponentialMartingale.{u} ∧
    certificate_brownianFirstPassageStableHalf.{u} ∧
    certificate_lampertiCompoundPoissonToBranchingLawNonexplosive.{u} ∧
    certificate_geometricLawInfinitelyDivisible ∧
    certificate_geometricStoppedRandomWalkInfinitelyDivisible.{u} ∧
    certificate_stableGammaIntegral ∧ certificate_randomWalkReversalLadderIdentity.{u} ∧
    certificate_mg1IdleRegulatorIdentity.{u} := by
  sorry
