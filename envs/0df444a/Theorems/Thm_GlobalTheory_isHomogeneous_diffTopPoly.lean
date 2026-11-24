-- Prove2me | Theorems.Thm_GlobalTheory_isHomogeneous_diffTopPoly
-- name    : GlobalTheory.isHomogeneous_diffTopPoly
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T22:57:21.808437+00:00
-- url     : https://prove2.me/theorems/c3242274-28df-4892-a841-fce7ac6f7c2c
-- title:
--   Global Theory: is Homogeneous diff Top Poly
-- statement:
--   The Global Theory construction uses the is Homogeneous diff Top Poly property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/ExistsMvPolynomialOfIteratedBackwardDifferenceVa.lean#L354-L358
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/ExistsMvPolynomialOfIteratedBackwardDifferenceVa.lean#L354-L358

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsMvPolynomialOfIteratedBackwardDifferenceVa
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open Finset
variable {G K : Type*} [AddCommGroup G] [Field K] [CharZero K]
omit [CharZero K]

theorem GlobalTheory.isHomogeneous_diffTopPoly (d : ℕ) {ι : Type*} [Fintype ι] [DecidableEq ι] (g : ι → G)
    (φ : G → K) (x : G) : (diffTopPoly d g φ x).IsHomogeneous d := by sorry
