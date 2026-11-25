-- Prove2me | Theorems.Thm_GlobalTheory_derivWeierstrassP_mul_eq
-- name    : GlobalTheory.derivWeierstrassP_mul_eq
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T00:08:27.24899+00:00
-- url     : https://prove2.me/theorems/f147e8b9-44ee-4d46-bcbc-d2bf12fab37d
-- title:
--   Global Theory: deriv Weierstrass P mul eq
-- statement:
--   The Global Theory construction uses the deriv Weierstrass P mul eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/AddMonoidHomEqZeroOfEventually.lean#L48-L62
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/AddMonoidHomEqZeroOfEventually.lean#L48-L62

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsVariableChangeEqLatticeCurve
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_WeierstrassCurvePointOfLatticeAddOfGeneric
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsNumeratorOfInvolution
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsMulEqPolynomialWeierstrassP
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_AddMonoidHomEqZeroOfEventually
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter PeriodPair Polynomial WeierstrassCurve UpperHalfPlane
open scoped Topology
noncomputable section
open GlobalTheory
variable {L L' : PeriodPair} {α : ℂ}

theorem GlobalTheory.derivWeierstrassP_mul_eq (hα : ∀ l ∈ L.lattice, α * l ∈ L'.lattice) {A D : ℂ[X]}
    (h : ∀ z, α * z ∉ L'.lattice → ℘[L'] (α * z) = A.eval (℘[L] z) / D.eval (℘[L] z))
    {z : ℂ} (hz : α * z ∉ L'.lattice) (hD : D.eval (℘[L] z) ≠ 0) :
    α * ℘'[L'] (α * z) =
      (derivative A * D - A * derivative D).eval (℘[L] z) / D.eval (℘[L] z) ^ 2 * ℘'[L] z := by sorry
