-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SiegLoc_HermOrth_trace_red_mul
-- name    : GlobalTheory.CompanionTheory.SiegLoc.HermOrth.trace_red_mul
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T12:13:34.680973+00:00
-- url     : https://prove2.me/theorems/08e53e61-f8ff-4274-a1a1-f92bcd054cb6
-- title:
--   Herm Orth: trace red mul
-- statement:
--   The Herm Orth construction uses the trace red mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/HermitianCharacterOrthogonality.lean#L40-L44
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/HermitianCharacterOrthogonality.lean#L40-L44

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_UnitarySchrodingerModel_LocalDefs
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ResAlgSplitTwo
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_FixedNondeg
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_UnramifiedQuotientCardStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_HermitianCharacterOrthogonality
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PositivityTheory.PfSWUS.Loc GlobalTheory.CompanionTheory.UnrDens GlobalTheory.CompanionTheory.SiegLoc Filter Topology
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SiegLoc GlobalTheory.CompanionTheory.SiegLoc.HermOrth
variable {R : Type} [CommRing R]

theorem GlobalTheory.CompanionTheory.SiegLoc.HermOrth.trace_red_mul (ϖ : R) (k n : ℕ) (b y : Matrix (Fin n) (Fin n) R) :
    Matrix.trace (red ϖ k b * red ϖ k y) = Ideal.Quotient.mk (lev ϖ k) (Matrix.trace (b * y)) := by sorry
