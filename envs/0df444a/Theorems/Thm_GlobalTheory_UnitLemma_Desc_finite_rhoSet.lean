-- Prove2me | Theorems.Thm_GlobalTheory_UnitLemma_Desc_finite_rhoSet
-- name    : GlobalTheory.UnitLemma.Desc.finite_rhoSet
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T21:28:13.632807+00:00
-- url     : https://prove2.me/theorems/2d5c6bff-9440-4468-8da3-0ac5b3b33e75
-- title:
--   Desc: finite rho Set
-- statement:
--   The Desc construction uses the finite rho Set property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/RhoPowLowerBoundSwappedPairs.lean#L66-L151
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/RhoPowLowerBoundSwappedPairs.lean#L66-L151

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_LinearDescent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_DltEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_FiniteIntegralClosureOfSeparableInvolutionAlgebrStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsInjectiveTorusClassesOfIdempotentDecomposiStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_RhoPowLowerBoundSwappedPairs
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Desc Polynomial Filter Topology
noncomputable section
open GlobalTheory GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Desc

theorem GlobalTheory.UnitLemma.Desc.finite_rhoSet (K : UQ) (B : InvAlg K) (hsep : B.P.Separable) (a : K.O) (ha : K.Small a) (k : ℕ) :
    Finite {c : B.T ⧸ (intUnits K.O B.A).subgroupOf B.T //
      IsIntegral K.O ((((Quotient.out c : B.T) : B.Aˣ)⁻¹ : B.Aˣ) * algebraMap K.O B.A a ^ k : B.A)} := by sorry
