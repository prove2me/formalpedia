-- Prove2me | Theorems.Thm_GlobalTheory_LatticeCovolumeL2_det_gram
-- name    : GlobalTheory.LatticeCovolumeL2.det_gram
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T00:00:34.968794+00:00
-- url     : https://prove2.me/theorems/32c3b017-7e55-4c6a-905f-62db407502fd
-- title:
--   Lattice Covolume L2: det gram
-- statement:
--   The Lattice Covolume L2 construction uses the det gram property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/ExistsLineBasis.lean#L76-L123
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/ExistsLineBasis.lean#L76-L123

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_ExistsLineBasis
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.LatticeCovolumeL2
open NumberField Matrix
variable {E : Type} [Field E] [NumberField E]

theorem GlobalTheory.LatticeCovolumeL2.det_gram {ι : Type} [Fintype ι] [DecidableEq ι] (hι : Fintype.card ι = Module.finrank ℚ E)
    (Ψ : Finset (E →+* ℂ)) (hΨ : ∀ τ : E →+* ℂ, τ ∈ Ψ ↔ ComplexEmbedding.conjugate τ ∉ Ψ)
    (a : ι → E) (s : Ψ → ℝ) (G : Matrix ι ι ℝ)
    (hG : ∀ k l, G k l = ∑ τ : Ψ, (τ.1 (a k) * (starRingEnd ℂ) (τ.1 (a l))).re * s τ) :
    G.det = |((Algebra.discr ℚ a : ℚ) : ℝ)| * (∏ τ, (s τ / 2)) ^ 2 := by sorry
