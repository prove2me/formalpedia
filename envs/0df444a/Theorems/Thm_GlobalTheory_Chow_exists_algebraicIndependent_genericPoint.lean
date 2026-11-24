-- Prove2me | Theorems.Thm_GlobalTheory_Chow_exists_algebraicIndependent_genericPoint
-- name    : GlobalTheory.Chow.exists_algebraicIndependent_genericPoint
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T11:09:32.256011+00:00
-- url     : https://prove2.me/theorems/ed66b01b-d147-40d7-a203-8695a3fbd6b4
-- title:
--   Chow: exists algebraic Independent generic Point
-- statement:
--   The Chow construction uses the exists algebraic Independent generic Point property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/ExistsAlgebraicIndependentGenericPoint.lean#L246-L273
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/ExistsAlgebraicIndependentGenericPoint.lean#L246-L273

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
omit [Fintype σ]

theorem GlobalTheory.Chow.exists_algebraicIndependent_genericPoint [Finite σ] {p : Ideal (MvPolynomial σ K)}
    [p.IsPrime] (hdim : ringKrullDim (MvPolynomial σ K ⧸ p) = (Fintype.card β : ℕ)) :
    ∃ κ : β → σ, AlgebraicIndependent K fun i => genericPoint p (κ i) := by sorry
