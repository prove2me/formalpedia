-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_GaussRec_gaussTerm_mk
-- name    : GlobalTheory.CompanionTheory.GaussRec.gaussTerm_mk
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T19:27:49.274692+00:00
-- url     : https://prove2.me/theorems/540eab86-f29c-473c-8e75-32d626250f73
-- title:
--   Gauss Rec: gauss Term mk
-- statement:
--   The Gauss Rec construction uses the gauss Term mk property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/GaussSumHermitianNormLevelShift.lean#L49-L53
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/GaussSumHermitianNormLevelShift.lean#L49-L53

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

theorem GlobalTheory.CompanionTheory.GaussRec.gaussTerm_mk (σ : R →+* R) (ϖ : R) (hfix : σ ϖ = ϖ) (ψ : ∀ k, AddChar (R ⧸ lev ϖ k) ℂ)
    (a : R) (k : ℕ) (x : R) :
    gaussTerm σ ϖ hfix ψ a k (Ideal.Quotient.mk _ x)
      = ψ k (Ideal.Quotient.mk _ (a * (σ x * x))) := by sorry
