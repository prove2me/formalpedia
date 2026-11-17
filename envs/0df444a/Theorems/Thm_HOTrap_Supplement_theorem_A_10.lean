-- Prove2me | Theorems.Thm_HOTrap_Supplement_theorem_A_10
-- name    : HOTrap.Supplement.theorem_A_10
-- status  : Open
-- author  : @iris
-- created : 2026-11-17T04:32:57.912141+00:00
-- url     : https://prove2.me/theorems/99c5caef-56a8-4c33-8d76-4ddeb88ab040
-- title:
--   Theorem A.10 — global minimization with a known term
-- statement:
--   Let $Y=\prod_{i=1}^k[a_i,b_i]$ with $a_i<b_i$ and $\operatorname{diam}(Y)\le D$. Let $p\ge1$, $\beta\in(0,1]$, $L_p\ge0$, $\nu=p+\beta$, let $f\in C^{p,\beta}(L_p)$ on a neighborhood of $Y$, and let $q$ be a known continuous function on $Y$.
--
--   For every $\delta>0$, a nonadaptively chosen set $V\subset Y$ exists with
--   $$
--   |V|\le C_{k,p,\beta}\max\left\{1,D^k(L_p/\delta)^{k/\nu}\right\}.
--   $$
--   There are explicit coefficient functions $L_v$, smooth near $Y$, with finite positive stability constant
--   $$
--   \Lambda_0=\sup_{y\in Y}\sum_{v\in V}|L_v(y)|.
--   $$
--   If supplied values satisfy $\max_{v\in V}|\widetilde f(v)-f(v)|\le\tau\le\delta/(8\Lambda_0)$, then the model $\widehat f=\sum_{v\in V}\widetilde f(v)L_v$ satisfies $\lVert\widehat f-f\rVert_{\infty,Y}\le\delta/4$. Every $\delta/2$-approximate minimizer $\widehat y$ of $\widehat f+q$ satisfies
--   $$
--   (f+q)(\widehat y)-\min_{y\in Y}(f+q)(y)\le\delta.
--   $$
--   Constructing and optimizing the model and evaluating $\widehat f(\widehat y)$ use no further query to $f$.
--
--   Differences from the source:
--   - encoding: sup-norm and attained-minimum notation → pointwise inequalities for every $y\in Y$; reason: equivalent because the nondegenerate rectangle is nonempty compact and all functions involved are continuous
--   - encoding: “explicit coefficient functions” → existential coefficient functions quantified before the unknown $f$, known term $q$, and supplied data; reason: a Lean witness supplies the construction while the quantifier order enforces nonadaptive independence
--   - encoding: $\Lambda_0<\infty$ together with the displayed division by $\Lambda_0$ → $0<\Lambda_0$ is recorded explicitly; reason: the constructed Lagrange family has $\Lambda_0\ge1$, and positivity excludes the undefined zero-denominator reading
--   - encoding: $\mathbb R^k$ with coordinates $1,\ldots,k$ → `EuclideanSpace ℝ (Fin k)` with zero-based coordinates; reason: this is the same finite-dimensional Euclidean space and product rectangle
-- source:
--   Zhou–Sugiyama–Suzuki, Finding Stationary Points under Higher-Order Smoothness: Trapping Algorithms and First-Order Lower Bounds, arXiv:2610.02791, Theorem A.10, p.64, Eq. (71)

import Mathlib
import Definitions.Def_HOTrap_HolderNear
import Definitions.Def_HOTrap_Supplement_hyperrectangle

namespace HOTrap.Supplement

/-- **Theorem A.10 (global minimization with a known term).** Zhou--Sugiyama--Suzuki,
*Finding Stationary Points under Higher-Order Smoothness: Trapping Algorithms and First-Order
Lower Bounds*, arXiv:2610.02791, Theorem A.10, p.64 (PDF p.67), Eq. (71).

The node set and coefficient functions occur before `f,q` and the supplied values, expressing the
paper's nonadaptive sampling.  The reconstructed model is the displayed finite sum, and every
`δ/2`-approximate minimizer of it plus the known term is `δ`-optimal for `f+q`.

**Formalization Note.** The universal constant is before the rectangle, `D,L_p,δ,f,q`, so it
depends only on `k,p,β`.  Uniform errors and approximate minima are written pointwise over `Y`,
which is equivalent to the paper's sup norm and attained minimum on this nonempty compact
rectangle.  Positivity of `Λ₀` is included as an existential property of the constructed stable
basis, making `δ/(8Λ₀)` nondegenerate.  The model uses only supplied values after the one batch. -/
theorem theorem_A_10 (k p : ℕ) (hk : 1 ≤ k) (hp : 1 ≤ p) (β : ℝ)
    (hβ0 : 0 < β) (hβ1 : β ≤ 1) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (a b : Fin k → ℝ), (∀ i, a i < b i) →
      ∀ D L δ ν : ℝ, 0 ≤ L → 0 < δ → ν = (p : ℝ) + β →
        Metric.diam (hyperrectangle a b) ≤ D →
        ∃ (V : Finset (EuclideanSpace ℝ (Fin k)))
          (Lv : EuclideanSpace ℝ (Fin k) → EuclideanSpace ℝ (Fin k) → ℝ) (Λ₀ : ℝ),
          (∀ v ∈ V, v ∈ hyperrectangle a b) ∧
          (V.card : ℝ) ≤ C * max 1
            (D ^ k * Real.rpow (L / δ) ((k : ℝ) / ν)) ∧
          (∀ v ∈ V, ∃ U : Set (EuclideanSpace ℝ (Fin k)),
            hyperrectangle a b ⊆ U ∧ IsOpen U ∧ ContDiffOn ℝ ⊤ (Lv v) U) ∧
          0 < Λ₀ ∧
          Λ₀ = sSup (Set.range (fun y : {y // y ∈ hyperrectangle a b} =>
            ∑ v ∈ V, |Lv v y|)) ∧
          ∀ (f q : EuclideanSpace ℝ (Fin k) → ℝ),
            HOTrap.HolderNear (hyperrectangle a b) p β L f →
            ContinuousOn q (hyperrectangle a b) →
            ∀ τ : ℝ, 0 ≤ τ → τ ≤ δ / (8 * Λ₀) →
            ∀ vals : EuclideanSpace ℝ (Fin k) → ℝ,
              (∀ v ∈ V, |vals v - f v| ≤ τ) →
              (∀ y ∈ hyperrectangle a b,
                |(∑ v ∈ V, vals v * Lv v y) - f y| ≤ δ / 4) ∧
              ∀ yhat ∈ hyperrectangle a b,
                (∀ y ∈ hyperrectangle a b,
                  (∑ v ∈ V, vals v * Lv v yhat) + q yhat ≤
                    (∑ v ∈ V, vals v * Lv v y) + q y + δ / 2) →
                ∀ y ∈ hyperrectangle a b, f yhat + q yhat - (f y + q y) ≤ δ := by sorry

end HOTrap.Supplement
