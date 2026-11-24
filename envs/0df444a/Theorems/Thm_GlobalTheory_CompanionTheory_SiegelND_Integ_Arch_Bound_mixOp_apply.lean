-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SiegelND_Integ_Arch_Bound_mixOp_apply
-- name    : GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.Bound.mixOp_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:01:26.234041+00:00
-- url     : https://prove2.me/theorems/1647771b-44bc-4408-bf06-489c7218cdf1
-- title:
--   Bound: mix Op apply
-- statement:
--   The Bound construction uses the mix Op apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/TupCoordApply.lean#L50-L51
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/TupCoordApply.lean#L50-L51

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_SecondCountableHermC
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_TupCoordApply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SiegelND GlobalTheory.CompanionTheory.SiegelND.Integ GlobalTheory.CompanionTheory.SiegelND.Integ.Arch GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.Bound
open MeasureTheory
open GlobalTheory.CompanionTheory.SiegelND.Integ.Arch
variable {W : Type} [Fintype W] {n M : ℕ}

theorem GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.Bound.mixOp_apply (J : W → Matrix (Fin M) (Fin M) ℂ) (z : TupV W n M) (k : W × Fin M) :
    mixOp J z k = (2 : ℂ) • ∑ j, J k.1 k.2 j • z (k.1, j) := by sorry

attribute [defeq] GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.Bound.mixOp_apply
