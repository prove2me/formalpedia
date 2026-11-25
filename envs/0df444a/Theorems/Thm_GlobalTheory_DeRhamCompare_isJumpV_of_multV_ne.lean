-- Prove2me | Theorems.Thm_GlobalTheory_DeRhamCompare_isJumpV_of_multV_ne
-- name    : GlobalTheory.DeRhamCompare.isJumpV_of_multV_ne
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T12:06:24.474548+00:00
-- url     : https://prove2.me/theorems/ed917a21-1aa6-41a3-bcd0-46bca5ffd31b
-- title:
--   De Rham Compare: is Jump V of mult V ne
-- statement:
--   The De Rham Compare construction uses the is Jump V of mult V ne property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ActQdRPeriodTEqCyclotomicBottom.lean#L201-L202
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ActQdRPeriodTEqCyclotomicBottom.lean#L201-L202

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_NonGaloisCusps_DualExactSequence
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_NonGaloisCusps_JumpMultiplicityDual
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CyclotomicCharacterPadicBasicProperties
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ActQdRPeriodTEqCyclotomicBottom
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.DeRhamCompare
open Module
open Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct
open GlobalTheory.IndefiniteRowSideFullHecke.JumpMultiplicityDual (mulPeriod tdR filDdR jumpMult)
variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
    {LL : Type} [Field LL] [Algebra Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    (ρ : Representation LL G V)

theorem GlobalTheory.DeRhamCompare.isJumpV_of_multV_ne {τ : K →ₐ[Qp] LL} {a : ℤ} (h : multV PD ρ τ a ≠ 0) :
    IsJumpV PD ρ τ a := by sorry
