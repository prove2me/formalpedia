-- Prove2me | Theorems.Thm_Noncritical
-- name    : Noncritical
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T20:31:21.181003+00:00
-- url     : https://prove2.me/theorems/8dde55d2-1573-4950-9162-bfbf77c5a9d8
-- title:
--   Noncritical: Noncritical
-- statement:
--   The paper's lem:noncritical (paper lines 154-162): for every `delta > 0` there are
--   `tau ∈ (0, 1/4)` and `C_delta < ∞`, depending only on `p, k, delta`, such that every
--   `p`-harmonic `v` on `B_1` with `‖v‖_{L^∞(B_1)} ≤ 1` and `|Dv(0)| > delta` satisfies
--   `‖v‖_{C^{k+1}(B_tau)} ≤ C_delta`.
--
--   The quantifier order is the paper's and is the whole point: `tau` and `C_delta` come BEFORE `v`.
--   That is the uniformity the compactness argument of section 2 needs and that the qualitative
--   Iwaniec-Manfredi regularity does not provide.
--
--   The proof is the paper's Schauder bootstrap on nested balls between `B_{2 tau}` and `B_tau`.
--   `GradientAnnulus` supplies `tau` and traps `Dv` in a convex set away from the origin;
--   `SmoothAwayFromCriticalInput` makes `v` smooth there, so the induction carries only
--   QUANTITATIVE bounds and no regularity; `DifferentiatedEqn` exhibits each directional derivative
--   `d_e v` as a weak solution of a linear divergence-form equation with coefficient field
--   `A x = D_xi A_p(Dv x)`; `FluxJacobianElliptic` gives that field explicit ellipticity constants
--   and bounded derivatives; `CoeffFieldBounds` gives it `C^{j,kappa}` control at no loss of order,
--   which is the step `norm_iteratedFDeriv_comp_le` cannot supply because a Holder seminorm is a
--   two-point difference; and `DivFormSchauderInput` then gains one order per round.
--
--   Source: https://github.com/na0b/phigherorder-lean/blob/1ab3890a96c86ab99822d51d99058a81269c2262/PHigherOrder/Noncritical.lean#L30-L262
-- source:
--   https://github.com/na0b/phigherorder-lean/blob/1ab3890a96c86ab99822d51d99058a81269c2262/PHigherOrder/Noncritical.lean#L30-L262

import Definitions.Def_PHigherOrder_BootstrapRound
import Definitions.Def_PHigherOrder_CoeffFieldFromScalarBounds
import Definitions.Def_PHigherOrder_DifferentiatedEqn
import Definitions.Def_PHigherOrder_DivFormSchauderInput
import Definitions.Def_PHigherOrder_FluxFieldBootstrapRound
import Definitions.Def_PHigherOrder_GradientFieldOrderShift
import Definitions.Def_PHigherOrder_GradientAnnulus
import Definitions.Def_PHigherOrder_PHarmRestrict
import Definitions.Def_PHigherOrder_PHarmWeakGradClassical
import Definitions.Def_PHigherOrder_SmoothAwayFromCriticalInput
import Definitions.Def_PHigherOrder_Noncritical
import Theorems.Thm_BootstrapRound
import Theorems.Thm_CoeffFieldFromScalarBounds
import Theorems.Thm_DifferentiatedEqn
import Theorems.Thm_FluxFieldBootstrapRound
import Theorems.Thm_GradientAnnulus
import Theorems.Thm_GradientFieldOrderShift
import Theorems.Thm_PHarmRestrict
import Theorems.Thm_PHarmWeakGradClassical

set_option autoImplicit false

theorem Noncritical (p : ℝ) (hp : 1 < p) (hp2 : p < 2) (k : ℕ)
    (F : FirstOrderEstimateInput p) (hsm : SmoothAwayFromCriticalInput p)
    (hS : DivFormSchauderInput) (δ : ℝ) (hδ : 0 < δ) :
    ∃ τ : ℝ, 0 < τ ∧ τ < 1 / 4 ∧ ∃ Cδ : ℝ, 0 < Cδ ∧
      ∀ (v : Plane → ℝ) (g : Plane → Plane), IsPHarm p (Metric.ball 0 1) v g →
        (∀ x ∈ Metric.ball (0 : Plane) 1, |v x| ≤ 1) → δ < ‖gradient v 0‖ →
        ContDiffOn ℝ ((k + 1 : ℕ) : ℕ∞) v (Metric.ball 0 τ) ∧
          ∀ i ≤ k + 1, ∀ x ∈ Metric.ball (0 : Plane) τ,
            ‖iteratedFDeriv ℝ i v x‖ ≤ Cδ := by sorry
