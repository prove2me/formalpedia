-- Prove2me | Theorems.Thm_HedgeContract_OPE_proposition_2_3
-- name    : HedgeContract.OPE.proposition_2_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T09:18:54.399003+00:00
-- url     : https://prove2.me/theorems/2ab25017-b0a7-4f9b-86aa-cd17e00874b1
-- title:
--   Proposition 2.3, p. 13 (PDF 15) — optimal reflected contract
-- statement:
--   Assume the standing model bounds and Assumption 6.2. Let $W$ be the principal's control value: for every initial promise $y\ge0$, it is the least upper bound of payoffs of admissible contracts. With $\bar y=\sup\{y\ge0:W(y)<\widetilde W(y)\}$, the set defining $\bar y$ is bounded. The value is $C^2$ on $(0,\infty)$, solves the HJB equation (29) for $0<y<\bar y$, has $W'(y)=-\delta$ for $y\ge\bar y$, and obeys $W(0)=\delta\Phi$ and $W''(\bar y)=0$.
--
--   For each promise $\hat y\ge0$, there is an admissible contract attaining $W(\hat y)$. Its immediate payment is $(\hat y-\bar y)^+$; before liquidation, its state stays in $[0,\bar y]$ and its subsequent payments are supported where $Y=\bar y$. The project is liquidated when $Y$ reaches zero. The controls are feedback selectors $(Z^*(Y),\zeta^*(Y))$ maximizing
--
--   $$\delta A^*(Z)+g(Z,\zeta)W'(Y)+\tfrac12\Sigma(Z,\zeta)W''(Y)\quad\text{over }(Z,\zeta)\in\mathcal Z\times\Gamma.$$
--
--   The corresponding market sensitivity is $U^*(Y)=\zeta^*(Y)-(\rho\psi/\sigma)Z^*(Y)$, as in equation (15). The theorem identifies a contract that actually attains the control value, not only a candidate solution of the HJB.
--
--   **Formalization Note.** The theorem uses the reduced Brownian formulation of (21) and (24). A real-valued least-upper-bound condition prevents a junk value from an empty or unbounded feasible set. Payments, including the time-zero lump sum, are charged by the Stieltjes payment measure. The feedback identity is asserted for Lebesgue-almost every time before liquidation.
-- source:
--   Huang, Ju & Xing, Optimal Contracting with Unobservable Managerial Hedging, working paper (Nov. 14, 2017), p. 13 (PDF 15), Proposition 2.3; proof §6.6, pp. 32–39 (PDF 34–41)

import Mathlib
import Definitions.Def_HedgeContract_OPE_Model
set_option autoImplicit false

namespace HedgeContract.OPE
open MeasureTheory Filter Topology
open scoped ENNReal NNReal

/-- Proposition 2.3: the optimal reflected contract attains the control value. -/
theorem proposition_2_3 (P : Params) (hP : P.Standing) (h62 : Assumption62 P)
    {Ω : Type*} [MeasurableSpace Ω] (P₀ : MeasureTheory.Measure Ω)
    [MeasureTheory.IsProbabilityMeasure P₀]
    (B : ℝ≥0 → Ω → Fin 2 → ℝ) (hB : Peng1990.SMP.IsStdBrownian P₀ B)
    (W : ℝ → ℝ) (hW : IsValue P P₀ B hB W) :
    BddAbove {y : ℝ | 0 ≤ y ∧ W y < Wtil P y} ∧
    ContDiffOn ℝ 2 W (Set.Ioi 0) ∧
    (∀ y ∈ Set.Ioo 0 (ybar P W),
      P.δ * W y = hamSup P y (deriv W y) (deriv (deriv W) y)) ∧
    (∀ y : ℝ, 0 ≤ y → ybar P W ≤ y →
      HasDerivWithinAt W (-P.δ) (Set.Ici 0) y) ∧
    W 0 = P.δ * P.Φ ∧
    derivWithin (derivWithin W (Set.Ici 0)) (Set.Ici 0) (ybar P W) = 0 ∧
    (∃ Zs ζs : ℝ → ℝ,
      (∀ y ∈ Set.Ioc 0 (ybar P W),
        IsMaximizer P (deriv W y) (deriv (deriv W) y) (Zs y) (ζs y)) ∧
      ∀ yhat : ℝ, 0 ≤ yhat → ∃ C : Contract Ω,
      C.Admissible P P₀ B hB yhat ∧
      C.payoff P P₀ = W yhat ∧
      (∀ᵐ ω ∂P₀,
        C.I 0 ω = max (yhat - ybar P W) 0 ∧
        (∀ t : ℝ≥0, (t : ℝ≥0∞) < C.τ ω → C.Y t ω ∈ Set.Icc 0 (ybar P W)) ∧
        C.paymentMeasure ω
          {t : ℝ | 0 < t ∧ ENNReal.ofReal t ≤ C.τ ω ∧
            C.Y t.toNNReal ω < ybar P W} = 0 ∧
        (C.τ ω < ⊤ → C.Y (C.τ ω).toReal.toNNReal ω = 0) ∧
        (∀ᵐ t : ℝ ∂MeasureTheory.volume,
          0 ≤ t → ENNReal.ofReal t < C.τ ω →
          C.Z t.toNNReal ω = Zs (C.Y t.toNNReal ω) ∧
          C.ζ t.toNNReal ω = ζs (C.Y t.toNNReal ω)))) := by sorry

end HedgeContract.OPE
