-- Prove2me | Theorems.Thm_OAI_IndependentProducts_integrated_first_exit_affine
-- name    : OAI.IndependentProducts.integrated_first_exit_affine
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T03:29:11.848414+00:00
-- url     : https://prove2.me/theorems/2acad2ac-f569-4bb8-bb72-a67c36540509
-- title:
--   Integrated affine lower bound for the excess of first-exit sums
-- statement:
--   Let $\mu$ be a probability measure on $\mathbb R$ with finite second moment and mean $\int w\,d\mu(w)=1$, put $C_\mu=2\big(\int w^2\,d\mu(w)\big)^{1/2}$ and assume $C_\mu>0$. Let $\iota$ be a finite index set and let $(\Omega,\nu)$ and $(\Lambda,\eta)$ be probability spaces. Let $B:\Lambda\times\iota\times\Omega\to\mathbb R$ be such that every section $B(\lambda,i,\cdot)$ is measurable and $\nu$-integrable, and let $U:\Lambda\to\mathbb R$ be $\eta$-integrable. For $b\in\Omega^\iota$, $w\in\mathbb R^\iota$ and $\lambda\in\Lambda$ define the first-exit sum
--
--   $$
--   Y(b,w,\lambda)=\sum_{i\in\iota}\Big(B(\lambda,i,b_i)\,w_i-\int_\Omega B(\lambda,i,\cdot)\,d\nu\Big),
--   $$
--
--   and let $\mathbf P=(\nu^{\otimes\iota}\otimes\mu^{\otimes\iota})\otimes\eta$ on $\Omega^\iota\times\mathbb R^\iota\times\Lambda$. Assume that $(b,\lambda)\mapsto\big(\sum_i B(\lambda,i,b_i)^2\big)^{1/2}$ is $\nu^{\otimes\iota}\otimes\eta$-integrable and that $Y$ is $\mathbf P$-integrable. Let $t,A,D\in\mathbb R$ with $A\ge0$, and suppose that the scalar estimate
--
--   $$
--   A\|a\|_2-Dr\le\int_{\mathbb R^\iota}\max\Big(t\,\Big|\beta+\sum_{i\in\iota}a_iw_i\Big|-r,\;0\Big)\,d\mu^{\otimes\iota}(w)
--   $$
--
--   holds for all $a\in\mathbb R^\iota$, $\beta\in\mathbb R$ and $r\ge0$, where $\|a\|_2=(\sum_i a_i^2)^{1/2}$. Then
--
--   $$
--   \frac{A}{C_\mu}\int|Y|\,d\mathbf P-D\int_\Lambda|U|\,d\eta\;\le\;\int\max\big(t\,|Y(b,w,\lambda)|-|U(\lambda)|,\;0\big)\,d\mathbf P(b,w,\lambda).
--   $$
--
--   The scalar hypothesis concerns a deterministic affine form in independent copies of the multiplier. The theorem upgrades it to first-exit sums with random coefficients: given an auxiliary variable $\lambda$ (in applications, the coordinates inside a finite head of the tree), the coefficients $B(\lambda,i,b_i)$ are independent across $i$, the multipliers $w_i$ are fresh, and the threshold $|U(\lambda)|$ may depend on $\lambda$. The size of $Y$ is measured by its $L^1$ norm, at the cost of the factor $C_\mu$.
--
--   **Formalization Note** $Y$ is `firstExitSum ν (B λ)` and the integrand on the right is `excess t |U λ| Y` with `excess t r z = max (t * |z| - r) 0`; the Euclidean length is `euclidSize`. The positivity of $C_\mu$ is an explicit hypothesis of the Lean statement (for a mean-one law it holds automatically).
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/ProductSpaces/ConditionalBounds.lean#L124-L173

import Mathlib
import Definitions.Def_IndependentProducts
import Definitions.Def_OAI_Analysis_ProductSpaces_TreeObstruction
import Definitions.Def_OAI_Analysis_ProductSpaces_PathMoments
import Definitions.Def_OAI_Analysis_ProductSpaces_WeakNullity
import Definitions.Def_OAI_Analysis_ProductSpaces_ScalarBounds
import Definitions.Def_OAI_Analysis_ProductSpaces_GaussianMoments
import Definitions.Def_OAI_Analysis_ProductSpaces_GaussianExcess
import Definitions.Def_OAI_Analysis_ProductSpaces_RandomSigns
import Definitions.Def_OAI_Analysis_ProductSpaces_MidpointModulus
import Definitions.Def_OAI_Analysis_ProductSpaces_ConditionalBounds

open OAI OAI.IndependentProducts
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology
universe uΛ uΩ uι
variable {ι : Type uι} {Ω : Type uΩ} {Λ : Type uΛ}
  [Fintype ι] [MeasurableSpace Ω] [MeasurableSpace Λ]
variable (μ : Measure ℝ) [IsProbabilityMeasure μ] (ν : Measure Ω) [IsProbabilityMeasure ν]
variable (η : Measure Λ) [IsProbabilityMeasure η]

theorem OAI.IndependentProducts.integrated_first_exit_affine
    (hμ : MemLp (fun w : ℝ => w) 2 μ) (hmean : ∫ w : ℝ, w ∂μ = 1)
    (B : Λ → ι → Ω → ℝ) (hB : ∀ old i, Integrable (B old i) ν)
    (hBm : ∀ old i, Measurable (B old i))
    (U : Λ → ℝ) (hU : Integrable U η)
    (hS : Integrable (fun z : (ι → Ω) × Λ => euclidSize (fun i => B z.2 i (z.1 i)))
      ((Measure.pi (fun _ : ι => ν)).prod η))
    (hY : Integrable (fun z : ((ι → Ω) × (ι → ℝ)) × Λ => firstExitSum ν (B z.2) z.1)
      (((Measure.pi (fun _ : ι => ν)).prod (Measure.pi (fun _ : ι => μ))).prod η))
    (t A D : ℝ) (hA : 0 ≤ A) (hC : 0 < 2 * Real.sqrt (∫ w : ℝ, w ^ 2 ∂μ))
    (hscalar : ∀ a : ι → ℝ, ∀ b r : ℝ, 0 ≤ r →
      A * euclidSize a - D * r ≤
        ∫ w : ι → ℝ, excess t r (b + ∑ i, a i * w i) ∂Measure.pi (fun _ : ι => μ)) :
    (A / (2 * Real.sqrt (∫ w : ℝ, w ^ 2 ∂μ))) *
      (∫ z : ((ι → Ω) × (ι → ℝ)) × Λ, |firstExitSum ν (B z.2) z.1|
        ∂((Measure.pi (fun _ : ι => ν)).prod (Measure.pi (fun _ : ι => μ))).prod η) -
      D * (∫ old, |U old| ∂η) ≤
      ∫ z : ((ι → Ω) × (ι → ℝ)) × Λ, excess t |U z.2| (firstExitSum ν (B z.2) z.1)
        ∂((Measure.pi (fun _ : ι => ν)).prod (Measure.pi (fun _ : ι => μ))).prod η := by sorry
