-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SiegLoc_GaussOne_sum_fixed_eq_zero
-- name    : GlobalTheory.CompanionTheory.SiegLoc.GaussOne.sum_fixed_eq_zero
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T12:13:42.063918+00:00
-- url     : https://prove2.me/theorems/53da8666-d811-4b9a-9fe6-490ef7527e02
-- title:
--   Gauss One: sum fixed eq zero
-- statement:
--   The Gauss One construction uses the sum fixed eq zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/GaussSumHermitianNormLevelOne.lean#L18-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/GaussSumHermitianNormLevelOne.lean#L18-L39

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_UnitarySchrodingerModel_LocalDefs
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ResAlgSplitTwo
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_FixedNondeg
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_UnramifiedQuotientCardStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ResidueAlgebraUnramifiedStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_NormFibreCardNonzeroStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_NormFibreCardZeroStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_GaussSumHermitianNormLevelOne
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PositivityTheory.PfSWUS.Loc GlobalTheory.CompanionTheory.UnrDens GlobalTheory.CompanionTheory.SiegLoc Filter Topology
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SiegLoc GlobalTheory.CompanionTheory.SiegLoc.GaussOne
variable {E : Type} [CommRing E] [Fintype E] {τ : E →+* E} {q : ℕ} {ε : ℤ}
open Classical

theorem GlobalTheory.CompanionTheory.SiegLoc.GaussOne.sum_fixed_eq_zero (χ : AddChar E ℂ) (A b : E) (hb : τ b = b) (hχ : χ (A * b) ≠ 1) :
    ∑ t ∈ Finset.univ.filter (fun t : E => τ t = t), χ (A * t) = 0 := by sorry
