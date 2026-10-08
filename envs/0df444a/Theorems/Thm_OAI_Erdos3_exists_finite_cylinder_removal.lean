-- Prove2me | Theorems.Thm_OAI_Erdos3_exists_finite_cylinder_removal
-- name    : OAI.Erdos3.exists_finite_cylinder_removal
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-08T11:06:52.999854+00:00
-- url     : https://prove2.me/theorems/92001a48-13b2-40b1-b219-c0bb6dfa3c99
-- title:
--   A finite cylinder removal chain leaves a weight of mean at most τ
-- statement:
--   Let $\Omega$ and $\iota$ be finite types ($\iota$ with decidable equality) and $X : \iota\to$ types, each $X_i$ finite with decidable equality. Let $\mu_i$ be a `FiniteProbabilityWeights (X i)` for each $i$ (nonnegative weights summing to $1$) with $(\mu_i).\mathrm{weight}(x)>0$ for all $i,x$; let $\mathrm{base}\in\prod_iX_i$, $p$ a `FiniteProbabilityWeights Ω`, and $F : \Omega\to\prod_iX_i$. Let $K,\tau,\eta$ be real numbers and $j,r$ natural numbers with $1\le K$, $0\le\tau$, $\eta\le 1$ and $2\le\tau K^{j+1}$, and assume `ProductMarginalsClose μ (observedProductDensity μ p F 1) η (j + r)`: for every $B\subseteq\iota$ with $|B|\le j+r$ and every $x$ of nonzero product weight, the mean of the density `observedProductDensity μ p F 1` (the density, with respect to the product of the $\mu_i$, of the push-forward of $p$ under $F$) over the coordinates outside $B$, with those in $B$ fixed to $x$ (OpenAI's `productConditionalMean μ B`), is within $\eta$ of $1$. Let $w : \Omega\to\mathbb{R}$ satisfy $0\le w(z)\le 1$ for all $z$. Then there exist $v : \Omega\to\mathbb{R}$ and a list $cs$ of `ProductCylinder X` (pairs $(S,a)$ of a finite set $S\subseteq\iota$ and an assignment $a\in\prod_{i\in S}X_i$) such that:
--
--   - `CylinderRemovalChain μ base p F K τ j r w v cs` holds: removing the cylinders of $cs$ in order from $w$ (each removal sets the weight to $0$ at those $z$ with $F(z)$ in the cylinder) ends at $v$, where each removed cylinder $c=(S,a)$ has $|S|\le j$, `c.mass` of the current `observedProductDensity` greater than $\tau$, and its `normalizedSection` satisfying OpenAI's `ProductBoundedMarginals … K r`;
--   - the length of $cs$ is at most the number of elements of `ProductCylinder.bounded (j + r)`, the finite set of cylinders $(S,a)$ with $|S|\le j+r$;
--   - the $p$-mean $\sum_z p.\mathrm{weight}(z)\,v(z)$ is at most $\tau$;
--   - $0\le v(z)\le 1$ for all $z$.
--
--   Lean: `OAI.Erdos3.exists_finite_cylinder_removal` in `lean/OAI/Combinatorics/Progressions/Estimates/RegularCylinderDecomposition.lean` (OpenAI); the definitions it uses are in the definitions bundles `OAIErdos3B011` of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Estimates/RegularCylinderDecomposition.lean#L298

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B011

namespace OAI

section

namespace Erdos3.ProductCylinder

variable {Ω ι : Type*} {X : ι → Type*}

variable [Fintype Ω] [Fintype ι] [DecidableEq ι] [∀ i, Fintype (X i)] [∀ i, DecidableEq (X i)]

end Erdos3.ProductCylinder

end

section

namespace Erdos3

end Erdos3

end

section

namespace Erdos3.ProductCylinder

variable {Ω ι : Type*} [Fintype Ω] [Fintype ι] [DecidableEq ι]
  {X : ι → Type*} [∀ i, Fintype (X i)] [∀ i, DecidableEq (X i)]
  (c : ProductCylinder X) (μ : ∀ i, FiniteProbabilityWeights (X i)) (base : ∀ i, X i)
  (p : FiniteProbabilityWeights Ω) (F : Ω → ∀ i, X i) (w : Ω → ℝ)

end Erdos3.ProductCylinder

end

section

namespace Erdos3.ProductCylinder

variable {Ω ι : Type*} [Fintype Ω] [Fintype ι] [DecidableEq ι]
  {X : ι → Type*} [∀ i, Fintype (X i)]
  (μ : ∀ i, FiniteProbabilityWeights (X i)) (base : ∀ i, X i)
  (p : FiniteProbabilityWeights Ω) (F : Ω → ∀ i, X i)

end Erdos3.ProductCylinder

end

section

namespace Erdos3

variable {Ω ι : Type*} {X : ι → Type*}

end Erdos3

end

section

namespace Erdos3

open ProductCylinder

theorem exists_finite_cylinder_removal {Ω ι : Type*} [Fintype Ω] [Fintype ι] [DecidableEq ι]
    {X : ι → Type*} [∀ i, Fintype (X i)] [∀ i, DecidableEq (X i)]
    (μ : ∀ i, FiniteProbabilityWeights (X i)) (hμ : ∀ i x, 0 < (μ i).weight x)
    (base : ∀ i, X i) (p : FiniteProbabilityWeights Ω) (F : Ω → ∀ i, X i)
    (K τ η : ℝ) (j r : ℕ) (hK : 1 ≤ K) (hτ : 0 ≤ τ) (hη : η ≤ 1)
    (hcut : 2 ≤ τ * K ^ (j + 1))
    (hbase : ProductMarginalsClose μ (observedProductDensity μ p F (fun _ => 1)) η (j + r))
    (w : Ω → ℝ) (hw0 : ∀ z, 0 ≤ w z) (hw1 : ∀ z, w z ≤ 1) :
    ∃ (v : Ω → ℝ) (cs : List (ProductCylinder X)),
      CylinderRemovalChain μ base p F K τ j r w v cs ∧
      cs.length ≤ (ProductCylinder.bounded (X := X) (j + r)).card ∧ p.mean v ≤ τ ∧
      (∀ z, 0 ≤ v z ∧ v z ≤ 1) := by
  sorry

end Erdos3
end
end OAI
