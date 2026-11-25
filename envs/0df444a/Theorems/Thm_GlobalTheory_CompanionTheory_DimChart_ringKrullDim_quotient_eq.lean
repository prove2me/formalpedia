-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_DimChart_ringKrullDim_quotient_eq
-- name    : GlobalTheory.CompanionTheory.DimChart.ringKrullDim_quotient_eq
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T02:59:47.928318+00:00
-- url     : https://prove2.me/theorems/d63e797d-adb3-53bb-9308-1d78c311f582
-- title:
--   Dim Chart: ring Krull Dim quotient eq
-- statement:
--   The Dim Chart construction uses the ring Krull Dim quotient eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/KrullDimQuotientEqTrdegSucc.lean#L41-L60
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/KrullDimQuotientEqTrdegSucc.lean#L41-L60

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

theorem GlobalTheory.CompanionTheory.DimChart.ringKrullDim_quotient_eq (Y : Scheme.{0}) (B : Type) [CommRing B] [Algebra ℤ B]
    [Algebra.FiniteType ℤ B] (j : Spec (.of B) ⟶ Y) [IsOpenImmersion j] (q : PrimeSpectrum B)
    (h0 : CharZero (Y.residueField (j q))) :
    ringKrullDim (B ⧸ q.asIdeal) =
      (((Algebra.trdeg ℤ (Y.residueField (j q))).toENat + 1 : ℕ∞) : WithBot ℕ∞) := by sorry
