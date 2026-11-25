-- Prove2me | Theorems.Thm_GlobalTheory_Chow_isPrincipal_elimIdeal
-- name    : GlobalTheory.Chow.isPrincipal_elimIdeal
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T11:58:38.632921+00:00
-- url     : https://prove2.me/theorems/fe067f5a-d68e-57d7-a850-c89d215c03fe
-- title:
--   Chow: is Principal elim Ideal
-- statement:
--   The Chow construction uses the is Principal elim Ideal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/ExistsAlgebraicIndependentGenericPoint.lean#L275-L349
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/ExistsAlgebraicIndependentGenericPoint.lean#L275-L349

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

theorem GlobalTheory.Chow.isPrincipal_elimIdeal [Nonempty β] {p : Ideal (MvPolynomial σ K)} [p.IsPrime]
    (hdim : ringKrullDim (MvPolynomial σ K ⧸ p) = (Fintype.card β : ℕ)) :
    (elimIdeal β p).IsPrincipal := by sorry
