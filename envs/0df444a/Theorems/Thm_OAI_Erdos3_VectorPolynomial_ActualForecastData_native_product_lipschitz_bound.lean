-- Prove2me | Theorems.Thm_OAI_Erdos3_VectorPolynomial_ActualForecastData_native_product_lipschitz_bound
-- name    : OAI.Erdos3.VectorPolynomial.ActualForecastData.native_product_lipschitz_bound
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-10-16T02:35:45.72+00:00
-- url     : https://prove2.me/theorems/b4943b61-c1fc-455a-b2b1-3143258cd2cb
-- title:
--   The product-twist Lipschitz constant for forecast data is at most e^(2P+1)
-- statement:
--   Let $X$ be a finite type with decidable equality, $m$ a natural number, $J_j$ ($j<m$) finite types, $N:X\to\mathbb{N}$, $\mathrm{originalpoly}_j$ vector polynomials on $X$ with values in $\mathbb{R}^{J_j}$, and $P_{\mathrm{native}},\mathrm{massLog},\mathrm{capLog},E$ real numbers (all implicit). Let $\mathrm{data}$ be an `ActualForecastData N originalpoly Pnative massLog capLog E` (a structure bundling a target, center constants and a finite combination of normalized twists with period cap, cover cap and Lipschitz constant $e^{3P_{\mathrm{native}}+3}$). Let $p_w,c_w,P_{\mathrm{test}}$ be reals and $L_w\ge0$, and let $W$ be a `NormalizedPolynomialTwist X (Σ j, J j) pw cw Lw`. Assume $P_{\mathrm{test}}\ge0$, $L_w\le e^{P_{\mathrm{test}}}$ and $c_w\le e^{P_{\mathrm{test}}}$. Then, computing in $\mathbb{R}_{\ge0}$ with $c_w^{+}=\max(c_w,0)$,
--   $$L_w\cdot\max\!\big(1,e^{3P_{\mathrm{native}}+3}\big)+e^{3P_{\mathrm{native}}+3}\cdot\max(1,c_w^{+})\le e^{2\max(P_{\mathrm{test}},\,3P_{\mathrm{native}}+3)+1}.$$
--   (The arguments $\mathrm{data}$ and $W$ fix the types and parameters but do not otherwise enter the inequality.)
--
--   Lean: `OAI.Erdos3.VectorPolynomial.ActualForecastData.native_product_lipschitz_bound` in `lean/OAI/Combinatorics/Progressions/Sampling/ActualForecastDataNativeProductBudget.lean` (OpenAI); the definitions it uses are in the definitions bundles `OAIErdos3B1351` of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Sampling/ActualForecastDataNativeProductBudget.lean#L580

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B1351

namespace OAI

section

namespace Erdos3.VectorPolynomial
open scoped NNReal

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open scoped NNReal

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped NNReal

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators NNReal

variable {X Ω Forecast : Type*} [Fintype X]
variable {Term : Forecast → Type*} {m : ℕ}
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open MeasureTheory
open scoped BigOperators Classical NNReal

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open scoped BigOperators Classical NNReal

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators NNReal

variable {X : Type*} [Fintype X] [DecidableEq X]
variable {m : ℕ} {J : Fin m → Type*} [∀ j, Fintype (J j)]

namespace ActualForecastData

variable (N : X → ℕ) (originalpoly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
variable (Pnative massLog capLog E : ℝ)

end ActualForecastData

variable {N : X → ℕ} {originalpoly : ∀ j, VectorPolynomial X ℝ (J j → ℝ)}
variable {Pnative massLog capLog E : ℝ} {F : Type*}

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial.ActualForecastData
open scoped BigOperators NNReal

variable {X : Type*} [Fintype X] [DecidableEq X]
variable {m : ℕ} {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable {N : X → ℕ} {originalpoly : ∀ j, VectorPolynomial X ℝ (J j → ℝ)}
variable {Pnative massLog capLog E : ℝ}
variable (data : ActualForecastData N originalpoly Pnative massLog capLog E)

theorem native_product_lipschitz_bound
    (_data : ActualForecastData N originalpoly Pnative massLog capLog E)
    {pw cw Ptest : ℝ} {Lw : ℝ≥0}
    (_W : NormalizedPolynomialTwist X (Σ j, J j) pw cw Lw)
    (hPtest : 0 ≤ Ptest) (hLw : (Lw : ℝ) ≤ Real.exp Ptest)
    (hcw : cw ≤ Real.exp Ptest) :
    ((Lw * max 1 (Real.toNNReal (Real.exp (3 * Pnative + 3))) +
      ⟨Real.exp (3 * Pnative + 3), Real.exp_nonneg _⟩ * max 1 (Real.toNNReal cw) : ℝ≥0) : ℝ) ≤
      Real.exp (2 * max Ptest (3 * Pnative + 3) + 1) := by
  sorry

end Erdos3.VectorPolynomial.ActualForecastData
end
end OAI
