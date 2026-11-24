-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_exists_close_of_hasseDeriv
-- name    : GroundTheory.PAdicHodge.exists_close_of_hasseDeriv
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T23:46:49.468965+00:00
-- url     : https://prove2.me/theorems/84c6aeef-9d90-4cff-8c44-8bbedb36f268
-- title:
--   PAdic Hodge: exists close of hasse Deriv
-- statement:
--   The PAdic Hodge construction uses the exists close of hasse Deriv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/AxLemma.lean#L171-L258
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/AxLemma.lean#L171-L258

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

theorem GroundTheory.PAdicHodge.exists_close_of_hasseDeriv (x : PadicAlgCl p) {ρ : ℝ}
    (hρ : ∀ σ : Gal(PadicAlgCl p/K), ‖σ x - x‖ ≤ ρ) {q : ℕ}
    (hq : q < (minpoly K x).natDegree) :
    ∃ b : PadicAlgCl p, (minpoly K b).natDegree ≤ (minpoly K x).natDegree - q ∧
      ‖((Nat.choose (minpoly K x).natDegree q : ℕ) : PadicAlgCl p)‖ *
        ‖x - b‖ ^ ((minpoly K x).natDegree - q) ≤ ρ ^ ((minpoly K x).natDegree - q) := by sorry
