-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_GaussRec_traceChar_mk
-- name    : GlobalTheory.CompanionTheory.GaussRec.traceChar_mk
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T19:28:40.742266+00:00
-- url     : https://prove2.me/theorems/07ea3979-0a16-4001-8085-cbed77934dd9
-- title:
--   Gauss Rec: trace Char mk
-- statement:
--   The Gauss Rec construction uses the trace Char mk property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/GaussSumHermitianNormLevelShift.lean#L61-L67
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/GaussSumHermitianNormLevelShift.lean#L61-L67

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

theorem GlobalTheory.CompanionTheory.GaussRec.traceChar_mk (σ : R →+* R) (ϖ : R) (hfix : σ ϖ = ϖ) (ψ : ∀ k, AddChar (R ⧸ lev ϖ k) ℂ)
    (c y : R) :
    traceChar σ ϖ hfix ψ c (Ideal.Quotient.mk _ y)
      = ψ 1 (Ideal.Quotient.mk _ (c * y + σ (c * y))) := by sorry
