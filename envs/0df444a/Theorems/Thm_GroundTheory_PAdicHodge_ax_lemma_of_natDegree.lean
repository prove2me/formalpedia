-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_ax_lemma_of_natDegree
-- name    : GroundTheory.PAdicHodge.ax_lemma_of_natDegree
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T23:46:34.925555+00:00
-- url     : https://prove2.me/theorems/743b8e58-021e-49b1-93f4-416dac8876ef
-- title:
--   PAdic Hodge: ax lemma of nat Degree
-- statement:
--   The PAdic Hodge construction uses the ax lemma of nat Degree property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/AxLemma.lean#L326-L433
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/AxLemma.lean#L326-L433

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_GaloisOnCp
import Definitions.Def_GroundTheory_PAdicHodge_AxLemma
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.PAdicHodge
open Polynomial
noncomputable section
variable {p : ℕ} [hp : Fact p.Prime] {K : IntermediateField ℚ_[p] (PadicAlgCl p)}

theorem GroundTheory.PAdicHodge.ax_lemma_of_natDegree (d : ℕ) : ∀ x : PadicAlgCl p, (minpoly K x).natDegree = d →
    ∀ ρ : ℝ, (∀ σ : Gal(PadicAlgCl p/K), ‖σ x - x‖ ≤ ρ) →
      ∃ y ∈ K, ‖x - y‖ ≤ (p : ℝ) ^ axExponent p (Nat.log p d) * ρ := by sorry
