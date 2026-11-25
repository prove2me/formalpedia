-- Prove2me | Theorems.Thm_GlobalTheory_Chow_elimIdeal_ne_bot
-- name    : GlobalTheory.Chow.elimIdeal_ne_bot
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T11:58:50.026191+00:00
-- url     : https://prove2.me/theorems/7bda251a-cfea-48b2-81ae-84f546c78fbc
-- title:
--   Chow: elim Ideal ne bot
-- statement:
--   The Chow construction uses the elim Ideal ne bot property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/ExistsAlgebraicIndependentGenericPoint.lean#L171-L242
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/ExistsAlgebraicIndependentGenericPoint.lean#L171-L242

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_AevalEqZeroOfHomogeneousComponent
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_ExistsAlgebraicIndependentGenericPoint
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
noncomputable section
open GlobalTheory GlobalTheory.Chow
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
variable {K : Type u} [Field K] {σ β : Type} [Fintype σ] [Fintype β]

theorem GlobalTheory.Chow.elimIdeal_ne_bot {p : Ideal (MvPolynomial σ K)} [hP : p.IsPrime]
    (hp : p.IsHomogeneous (homogeneousSubmodule σ K)) (hX : ∃ j, X j ∉ p)
    (hdim : ringKrullDim (MvPolynomial σ K ⧸ p) ≤ (Fintype.card β : ℕ)) : elimIdeal β p ≠ ⊥ := by sorry
