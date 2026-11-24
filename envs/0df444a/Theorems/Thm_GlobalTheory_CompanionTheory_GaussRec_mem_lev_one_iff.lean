-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_GaussRec_mem_lev_one_iff
-- name    : GlobalTheory.CompanionTheory.GaussRec.mem_lev_one_iff
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T11:43:45.808077+00:00
-- url     : https://prove2.me/theorems/e9e43a97-f94c-468e-86fd-6b21338f23f5
-- title:
--   Gauss Rec: mem lev one iff
-- statement:
--   The Gauss Rec construction uses the mem lev one iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/GaussSumHermitianNormLevelShift.lean#L111-L128
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/GaussSumHermitianNormLevelShift.lean#L111-L128

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

theorem GlobalTheory.CompanionTheory.GaussRec.mem_lev_one_iff {σ : R →+* R} {ϖ : R} {q : ℕ} {ε : ℤ} (hR : IsUnrQuad R σ ϖ q ε) {a : R}
    (ha : σ a = a) (ha1 : a ∉ lev ϖ 1) (x : R) : a * σ x ∈ lev ϖ 1 ↔ x ∈ lev ϖ 1 := by sorry
