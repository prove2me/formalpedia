-- Prove2me | Theorems.Thm_NumStochOpt_Bounds_edmundson_madansky_independent_components
-- name    : NumStochOpt.Bounds.edmundson_madansky_independent_components
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-30T19:31:36.460391+00:00
-- url     : https://prove2.me/theorems/3a4d3643-63f5-46dc-8e18-8e762206d9a5
-- title:
--   Edmundson–Madansky upper bound for a random vector with independent components on a box
-- statement:
--   Let $\xi=(\xi_1,\dots,\xi_m)$ be a random vector on a probability space $(\Omega,P)$ whose components are independent, with $\xi_j\in[a_j,b_j]$ almost surely, $a_j<b_j$, and expectations $\xi^0_j=E\xi_j$. Let $\hat\xi$ be the discrete random vector with independent components $\hat\xi_j$ distributed on $\{a_j,b_j\}$ according to (2.32):
--   $$
--   P\{\hat\xi_j=a_j\}=\frac{b_j-\xi^0_j}{b_j-a_j},\qquad P\{\hat\xi_j=b_j\}=\frac{\xi^0_j-a_j}{b_j-a_j}.
--   $$
--   $\hat\xi$ takes values only at the $2^m$ vertices of the rectangle $\Xi=\times_{j=1}^m[a_j,b_j]$. If $\varphi$ is convex on $\Xi$, then
--   $$
--   E\varphi(\xi)\;\le\;E\varphi(\hat\xi)=\sum_{v}\Big(\prod_{j=1}^m p_j(v_j)\Big)\varphi(v),
--   $$
--   the sum over the vertices $v=(v_1,\dots,v_m)$ of $\Xi$, where $p_j(a_j)$ and $p_j(b_j)$ are the two probabilities above.
--
--   With $\varphi=Q(x,\cdot)$, convex in $(h,T)$ by property (b), this is the multivariate form of the upper bound (2.33) on the expected recourse cost, and applied blockwise it gives the partitioned bound (2.37).
--
--   **Formalization Note** The book states the result for $\varphi=Q(x,\cdot)$; it is stated here for any function convex on the box, with the explicit vertex weights instead of a random vector $\hat\xi$. Independence of the components is essential: for dependent components with the same means the inequality fails in general. The components are indexed by a finite type; $a_j<b_j$ excludes the division by zero in (2.32).
-- source:
--   P. Kall, A. Ruszczyński, K. Frauendorfer, "Approximation Techniques in Stochastic Programming", in Ermoliev & Wets (eds.), Numerical Techniques for Stochastic Optimization, Springer 1988, Ch. 2, p. 46, Edmundson-Madansky inequality for independent components (with (2.32)-(2.33))

import Mathlib
import Definitions.Def_NumStochOpt_Bounds_EdmundsonMadansky

open MeasureTheory

namespace NumStochOpt.Bounds

/-- The Edmundson–Madansky bound for independent components, p. 46 (with (2.32)–(2.33)). Let
`ξ = (ξ_j)_{j ∈ ι}` have independent components, `ξ_j ∈ [a_j, b_j]` almost surely with
`a_j < b_j`, and means `ξ⁰_j = E ξ_j`. If `φ` is convex on the box `Ξ = ×_j [a_j, b_j]`, then
`E φ(ξ) ≤ Σ_v (∏_j p_j(v_j)) φ(v)`, the sum over the vertices `v` of `Ξ`, where `p_j(a_j) =
(b_j − ξ⁰_j)/(b_j − a_j)` and `p_j(b_j) = (ξ⁰_j − a_j)/(b_j − a_j)`. -/
theorem edmundson_madansky_independent_components {Ω ι : Type*} [MeasurableSpace Ω]
    [Fintype ι] [DecidableEq ι] (P : Measure Ω) [IsProbabilityMeasure P] (ξ : Ω → ι → ℝ)
    (hmeas : ∀ j, AEMeasurable (fun ω => ξ ω j) P)
    (hind : ProbabilityTheory.iIndepFun (fun j ω => ξ ω j) P)
    (a b : ι → ℝ) (hab : ∀ j, a j < b j)
    (hsupp : ∀ᵐ ω ∂P, ∀ j, ξ ω j ∈ Set.Icc (a j) (b j))
    (φ : (ι → ℝ) → ℝ) (hφ : ConvexOn ℝ (Set.pi Set.univ fun j => Set.Icc (a j) (b j)) φ) :
    ∫ ω, φ (ξ ω) ∂P ≤ emUpperBound a b (fun j => ∫ ω, ξ ω j ∂P) φ := by sorry

end NumStochOpt.Bounds
