-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SiegelND_Integ_Arch_Bound_polarOp_apply
-- name    : GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.Bound.polarOp_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:04:54.936067+00:00
-- url     : https://prove2.me/theorems/35e17027-75e3-4b62-a883-2ebed3e43d9f
-- title:
--   Bound: polar Op apply
-- statement:
--   The Bound construction uses the polar Op apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/TupCoordApply.lean#L57-L58
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/TupCoordApply.lean#L57-L58

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

theorem GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.Bound.polarOp_apply (J : W → Matrix (Fin M) (Fin M) ℂ) (b : W → Matrix (Fin n) (Fin n) ℂ)
    (y : TupV W n M) : polarOp J b y = mixOp J (diagOp b y) := by sorry
