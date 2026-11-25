-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_DimChart_trdeg_int_eq_of_isFractionRing
-- name    : GlobalTheory.CompanionTheory.DimChart.trdeg_int_eq_of_isFractionRing
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T02:52:02.696738+00:00
-- url     : https://prove2.me/theorems/679de5b1-451e-4c10-891c-8957c0981635
-- title:
--   Dim Chart: trdeg int eq of is Fraction Ring
-- statement:
--   The Dim Chart construction uses the trdeg int eq of is Fraction Ring property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/KrullDimQuotientEqTrdegSucc.lean#L23-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/KrullDimQuotientEqTrdegSucc.lean#L23-L33

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_PIntDomainDim
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_KrullDimQuotientEqTrdegSucc
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.DimChart

theorem GlobalTheory.CompanionTheory.DimChart.trdeg_int_eq_of_isFractionRing (A : Type) [CommRing A] [IsDomain A] [Algebra ℤ A] (L : Type)
    [Field L] [Algebra ℤ L] [Algebra A L] [IsFractionRing A L]
    (hA : Function.Injective (algebraMap ℤ A)) :
    Algebra.trdeg ℤ A = Algebra.trdeg ℤ L := by sorry
