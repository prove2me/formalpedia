-- Prove2me | Theorems.Thm_OAI_Erdos3_VectorPolynomial_ActualForecastData_native_product_bounds
-- name    : OAI.Erdos3.VectorPolynomial.ActualForecastData.native_product_bounds
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-10-16T02:38:50.565135+00:00
-- url     : https://prove2.me/theorems/54fb2e92-a28f-4384-8fad-b970735d3f7b
-- title:
--   Product twists of forecast data have Lipschitz, cover and modulus at most e^(2P+1)
-- statement:
--   Let $X$ be a finite type with decidable equality, $m$ a natural number, $J_j$ ($j<m$) finite types, $N:X\to\mathbb{N}$, $\mathrm{originalpoly}_j$ vector polynomials on $X$ with values in $\mathbb{R}^{J_j}$, and $P_{\mathrm{native}},\mathrm{massLog},\mathrm{capLog},E$ real numbers (all implicit). Let $\mathrm{data}$ be an `ActualForecastData N originalpoly Pnative massLog capLog E` (a structure bundling a complex target on `integerBox N`, center constants, a finite type $\mathrm{data.Term}$, complex coefficients, and for each term $i$ a `NormalizedPolynomialTwist` $\mathrm{data.twists}_i$ whose period cap, cover cap and Lipschitz constant are all $e^{3P_{\mathrm{native}}+3}$). Let $p_w,c_w,P_{\mathrm{test}}$ be reals and $L_w\ge0$, and let $W$ be a `NormalizedPolynomialTwist X (Σ j, J j) pw cw Lw` (a structure bundling a positive modulus at most $p_w$, a positive cover at most $c_w$, a mask and an $L_w$-Lipschitz smooth function bounded by $1$). Assume $P_{\mathrm{test}}\ge0$, $L_w\le e^{P_{\mathrm{test}}}$, $p_w\le e^{P_{\mathrm{test}}}$ and $c_w\le e^{P_{\mathrm{test}}}$. Put $P=\max(P_{\mathrm{test}},3P_{\mathrm{native}}+3)$. Then for every term $i$:
--   $$L_w\cdot\max\!\big(1,e^{3P_{\mathrm{native}}+3}\big)+e^{3P_{\mathrm{native}}+3}\cdot\max(1,c_w^{+})\le e^{2P+1},$$
--   (computed in $\mathbb{R}_{\ge0}$, with $c_w^{+}=\max(c_w,0)$), $W.\mathrm{cover}\cdot(\mathrm{data.twists}_i).\mathrm{cover}\le e^{2P+1}$, and $W.\mathrm{modulus}\cdot(\mathrm{data.twists}_i).\mathrm{modulus}\le e^{2P+1}$.
--
--   Lean: `OAI.Erdos3.VectorPolynomial.ActualForecastData.native_product_bounds` in `lean/OAI/Combinatorics/Progressions/Sampling/ActualForecastDataNativeProductBudget.lean` (OpenAI); the definitions it uses are in the definitions bundles `OAIErdos3B1351` of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Sampling/ActualForecastDataNativeProductBudget.lean#L617

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

theorem native_product_bounds
    {pw cw Ptest : ℝ} {Lw : ℝ≥0}
    (W : NormalizedPolynomialTwist X (Σ j, J j) pw cw Lw)
    (hPtest : 0 ≤ Ptest) (hLw : (Lw : ℝ) ≤ Real.exp Ptest)
    (hpw : pw ≤ Real.exp Ptest) (hcw : cw ≤ Real.exp Ptest) :
    let P := max Ptest (3 * Pnative + 3)
    ∀ i : data.Term,
      ((Lw * max 1 (Real.toNNReal (Real.exp (3 * Pnative + 3))) +
        ⟨Real.exp (3 * Pnative + 3), Real.exp_nonneg _⟩ * max 1 (Real.toNNReal cw) : ℝ≥0) : ℝ) ≤
          Real.exp (2 * P + 1) ∧
      ((W.cover * (data.twists i).cover : ℕ) : ℝ) ≤ Real.exp (2 * P + 1) ∧
      ((W.modulus * (data.twists i).modulus : ℕ) : ℝ) ≤ Real.exp (2 * P + 1) := by
  sorry

end Erdos3.VectorPolynomial.ActualForecastData
end
end OAI
