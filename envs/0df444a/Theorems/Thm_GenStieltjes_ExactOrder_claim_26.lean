-- Prove2me | Theorems.Thm_GenStieltjes_ExactOrder_claim_26
-- name    : GenStieltjes.ExactOrder.claim_26
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T13:46:22.693504+00:00
-- url     : https://prove2.me/theorems/8cf7a24d-cd17-4e9b-8272-fc5995206181
-- title:
--   Proof of Theorem 16, claim (26) — $\int\Phi(y)\,dy/(1+y)^{\alpha+1}<\infty\Rightarrow\int d\Phi(y)/(1+y)^{\alpha}<\infty$
-- statement:
--   Let $\alpha>0$, let $\nu$ be a measure on $[0,\infty)$, and let $\Phi(y)=\nu([0,y))$ be its left-continuous distribution function (so $d\Phi=\nu$ on $[0,\infty)$ and $\Phi(0)=0$). If
--   $$\int_{[0,\infty)}\frac{\Phi(y)\,dy}{(1+y)^{\alpha+1}}<\infty,$$
--   then
--   $$\int_{[0,\infty)}\frac{d\Phi(y)}{(1+y)^{\alpha}}<\infty\qquad\text{and}\qquad \lim_{t\to\infty}\Phi(t)(1+t)^{-\alpha}=0 .$$
--
--   In the proof of Theorem 16 this is the step that turns the integrability of the fractional integral $I^+_{1-\varepsilon}\mu_\beta$ (whose density is $\Phi/\Gamma(1-\varepsilon)$) into the statement that the measure with distribution function proportional to $\Phi$ lies in $\mathcal M_\alpha$.
--
--   **Formalization Note** The paper states (26) for the specific $\Phi$ of (25); here it is stated for the distribution function of an arbitrary measure on $[0,\infty)$, which is the generality its integration-by-parts argument proves. The limit is the intermediate claim proved in the same passage. Values are in $[0,\infty]$.
-- source:
--   Karp & Prilepkina, Generalized Stieltjes transforms: basic aspects, arXiv:1111.4271v2, p. 11, proof of Theorem 16, claim (26)

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P11
import Definitions.Def_GenStieltjes_ExactOrder_Basic

namespace GenStieltjes.ExactOrder

open MeasureTheory
open scoped NNReal ENNReal
open QAlgorithms.Papers.Independent.Renew46.P11 (PositiveReal StieltjesRepresentation StieltjesClass)

/-- Claim (26), proof of Theorem 16, p. 11, for a general left-continuous distribution
function `Φ = F_ν` of a measure `ν` on `[0, ∞)`: if `∫_{[0,∞)} Φ(y) dy / (1 + y)^{α+1} < ∞`
then `∫_{[0,∞)} dΦ(y) / (1 + y)^α < ∞` (i.e. `ν ∈ M_α`), and `Φ(t)(1 + t)^{−α} → 0`
as `t → ∞`. -/
theorem claim_26 (α : ℝ) (hα : 0 < α) (ν : Measure ℝ≥0)
    (h : ∫⁻ y in Set.Ioi (0 : ℝ),
        distFn ν y.toNNReal * ENNReal.ofReal ((1 + y) ^ (-(α + 1))) < ⊤) :
    InM α ν ∧
      Filter.Tendsto (fun t : ℝ≥0 => distFn ν t * ENNReal.ofReal ((1 + (t : ℝ)) ^ (-α)))
        Filter.atTop (nhds 0) := by sorry

end GenStieltjes.ExactOrder
