-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_GaussRec_mk_lft
-- name    : GlobalTheory.CompanionTheory.GaussRec.mk_lft
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T19:26:17.825913+00:00
-- url     : https://prove2.me/theorems/5d2ff513-0a26-4e59-a69a-37c5e695872a
-- title:
--   Gauss Rec: mk lft
-- statement:
--   The Gauss Rec construction uses the mk lft property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/GaussSumHermitianNormLevelShift.lean#L133-L135
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/GaussSumHermitianNormLevelShift.lean#L133-L135

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_UnitarySchrodingerModel_LocalDefs
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ResAlgSplitTwo
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_FixedNondeg
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_UnramifiedQuotientCardStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_GaussSumHermitianNormLevelShift
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PositivityTheory.PfSWUS.Loc GlobalTheory.CompanionTheory.UnrDens GlobalTheory.CompanionTheory.SiegLoc Filter Topology
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.GaussRec
variable {R : Type} [CommRing R]

theorem GlobalTheory.CompanionTheory.GaussRec.mk_lft (ϖ : R) (k : ℕ) (w : R ⧸ lev ϖ k) :
    Ideal.Quotient.mk (lev ϖ k) (lft ϖ k w) = w := by sorry
