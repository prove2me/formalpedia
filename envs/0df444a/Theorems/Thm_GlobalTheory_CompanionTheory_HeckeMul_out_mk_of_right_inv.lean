-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_HeckeMul_out_mk_of_right_inv
-- name    : GlobalTheory.CompanionTheory.HeckeMul.out_mk_of_right_inv
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T11:46:39.145806+00:00
-- url     : https://prove2.me/theorems/258f1e8b-0eaa-4577-ba9b-dd175f858331
-- title:
--   Hecke Mul: out mk of right inv
-- statement:
--   The Hecke Mul construction uses the out mk of right inv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/FinsumOutTranslate.lean#L14-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/FinsumOutTranslate.lean#L14-L19

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_ArchimedeanBaseChange_ArchimedeanBaseChangeProof_SatakeExponents_UniformizerValuations_SubOfNonNil
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_FinsumOutTranslate
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory GlobalTheory.SmGL GlobalTheory.PRep PositivityTheory.Rg.BcN.F2 Pointwise
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.HeckeMul
variable {G : Type} [Group G]

theorem GlobalTheory.CompanionTheory.HeckeMul.out_mk_of_right_inv {M : Type} (K : Subgroup G) (φ : G → M)
    (hφ : ∀ x, ∀ k ∈ K, φ (x * k) = φ x) (x : G) :
    φ (QuotientGroup.mk x : G ⧸ K).out = φ x := by sorry
