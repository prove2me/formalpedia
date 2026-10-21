-- Prove2me | Theorems.Thm_HedgeContract_OPE_proposition_6_4
-- name    : HedgeContract.OPE.proposition_6_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T09:18:53.527992+00:00
-- url     : https://prove2.me/theorems/d6903f64-34d0-49b4-b3dc-ed7cb15c0fb5
-- title:
--   Proposition 6.4, p. 35 (PDF 37) — free-boundary HJB and concavity
-- statement:
--   Assume the standing model bounds and all six parts of Assumption 6.2. Let $W(y)$ be the least upper bound of admissible principal payoffs from every $y\ge0$, and let $\bar y=\sup\{y\ge0:W(y)<\widetilde W(y)\}$. The set defining $\bar y$ is bounded above. The value is $C^2$ on $(0,\infty)$ and, for $0<y<\bar y$, satisfies
--
--   $$\delta W(y)=\sup_{(Z,\zeta)\in\mathcal Z\times\Gamma}\left\{\delta(\mu+A^*(Z))+(ry+g(Z,\zeta))W'(y)+\tfrac12\Sigma(Z,\zeta)W''(y)\right\}.$$
--
--   Moreover $W'(y)=-\delta$ for $y\ge\bar y$, $W(0)=\delta\Phi$, and $W''(\bar y)=0$. The value is concave on $[0,\infty)$ and strictly concave on $[0,\bar y)$.
--
--   This is the regularity and value-shape result used to identify the payment boundary and the controls in Proposition 2.3.
--
--   **Formalization Note.** Derivatives at $\bar y=0$ are taken within $[0,\infty)$. The Hamiltonian supremum is over the compact control box.
-- source:
--   Huang, Ju & Xing, Optimal Contracting with Unobservable Managerial Hedging, working paper (Nov. 14, 2017), p. 35 (PDF 37), Proposition 6.4

import Mathlib
import Definitions.Def_HedgeContract_OPE_Model
set_option autoImplicit false

namespace HedgeContract.OPE
open MeasureTheory Filter Topology
open scoped ENNReal NNReal

/-- Proposition 6.4: regularity, the free-boundary HJB equation, and concavity. -/
theorem proposition_6_4 (P : Params) (hP : P.Standing) (h62 : Assumption62 P)
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
    ConcaveOn ℝ (Set.Ici 0) W ∧
    StrictConcaveOn ℝ (Set.Ico 0 (ybar P W)) W := by sorry

end HedgeContract.OPE
