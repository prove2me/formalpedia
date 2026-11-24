-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_GaussRec_gaussTerm_mul
-- name    : GlobalTheory.CompanionTheory.GaussRec.gaussTerm_mul
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T11:44:03.577297+00:00
-- url     : https://prove2.me/theorems/a41ab56a-0484-48d5-baee-51865ef46c75
-- title:
--   Gauss Rec: gauss Term mul
-- statement:
--   The Gauss Rec construction uses the gauss Term mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/GaussSumHermitianNormLevelShift.lean#L189-L196
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/GaussSumHermitianNormLevelShift.lean#L189-L196

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

theorem GlobalTheory.CompanionTheory.GaussRec.gaussTerm_mul {σ : R →+* R} {ϖ : R} (hfix : σ ϖ = ϖ)
    {ψ : ∀ k, AddChar (R ⧸ lev ϖ k) ℂ} (hψ : IsLevelChars σ ϖ ψ) (j : ℕ) (a x : R) :
    gaussTerm σ ϖ hfix ψ a (j + 2) (Ideal.Quotient.mk _ (ϖ * x))
      = gaussTerm σ ϖ hfix ψ a j (Ideal.Quotient.mk _ x) := by sorry
