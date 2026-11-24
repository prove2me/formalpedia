-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_GaussRec_sum_filter_eq
-- name    : GlobalTheory.CompanionTheory.GaussRec.sum_filter_eq
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T11:43:44.822798+00:00
-- url     : https://prove2.me/theorems/dfb01da4-8256-4fa9-bbf8-730e05f1947d
-- title:
--   Gauss Rec: sum filter eq
-- statement:
--   The Gauss Rec construction uses the sum filter eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/GaussSumHermitianNormLevelShift.lean#L198-L229
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/GaussSumHermitianNormLevelShift.lean#L198-L229

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

theorem GlobalTheory.CompanionTheory.GaussRec.sum_filter_eq {σ : R →+* R} {ϖ : R} {q : ℕ} {ε : ℤ} (hR : IsUnrQuad R σ ϖ q ε)
    [∀ k, Fintype (R ⧸ lev ϖ k)] {ψ : ∀ k, AddChar (R ⧸ lev ϖ k) ℂ} (hψ : IsLevelChars σ ϖ ψ)
    (j : ℕ) {a : R} (ha : σ a = a) (ha1 : a ∉ lev ϖ 1) [DecidablePred fun c => c ∈ lev ϖ 1] :
    (∑ w, if a * σ (lft ϖ (j + 2) w) ∈ lev ϖ 1 then gaussTerm σ ϖ hR.fix_ϖ ψ a (j + 2) w else 0)
      = ∑ w' : R ⧸ lev ϖ (j + 1), gaussTerm σ ϖ hR.fix_ϖ ψ a j
          (Ideal.Quotient.factor (Ideal.span_singleton_le_span_singleton.2 (pow_dvd_pow ϖ (Nat.le_succ j))) w') := by sorry
