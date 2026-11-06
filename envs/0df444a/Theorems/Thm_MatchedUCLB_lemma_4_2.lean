-- Prove2me | Theorems.Thm_MatchedUCLB_lemma_4_2
-- name    : MatchedUCLB.lemma_4_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T01:31:47.998001+00:00
-- url     : https://prove2.me/theorems/c54edaaf-d92e-4fdc-89f9-58908b304da7
-- title:
--   Lemma 4.2 — the smooth maximum $M_\delta$ is $C^\infty$, convex, monotone, and exact away from the diagonal
-- statement:
--   Let $\delta>0$ and let $M_\delta(a,b)=a+\psi_\delta(b-a)$ be the smooth maximum of Definition 4.1. Then:
--
--   1. $M_\delta$ is $C^\infty$ and jointly convex on $\mathbb R^2$, and nondecreasing in each argument;
--   2. for all $a,b\in\mathbb R$,
--   $$
--   \max\{a,b\}\ \le\ M_\delta(a,b)\ \le\ \max\{a,b\}+\frac{\delta}{2};
--   $$
--   3. $M_\delta(a,b)=a$ if $a-b\ge\delta$, and $M_\delta(a,b)=b$ if $b-a\ge\delta$.
--
--   The smooth maximum is the gluing device of the construction: it joins the base formulas in (4.4) and the chain with its affine continuation in (4.12d), and part 3 guarantees exact agreement with the dominant formula, so derivatives and oracle outputs are preserved there.
--
--   **Formalization Note** $C^\infty$ is `ContDiff ℝ ∞` of $(a,b)\mapsto M_\delta(a,b)$ on $\mathbb R\times\mathbb R$.
--
--   Differences from the source: none.
-- source:
--   Bai, Tight Lower Bounds under Matched High-Order Hölder Smoothness and Uniform Convexity, arXiv:2611.05527, Lemma 4.2, p.5

import Mathlib
import Definitions.Def_MatchedUCLB_smoothMax

open scoped ContDiff Topology

namespace MatchedUCLB

/-- **Lemma 4.2 (smooth maximum).** Bai, *Tight Lower Bounds under Matched High-Order Hölder Smoothness and Uniform Convexity*, arXiv:2611.05527, Lemma 4.2, p.5 (citing [Aza13, Lemma 1]): "For every
`δ > 0`, the function `M_δ` in Definition 4.1 is `C^∞`, convex, and nondecreasing in each argument.
For all `a, b ∈ ℝ`, `max{a, b} ≤ M_δ(a, b) ≤ max{a, b} + δ/2`, `M_δ(a, b) = a` if `a − b ≥ δ`, and
`= b` if `b − a ≥ δ`."

**Formalization Note.** `C^∞` is `ContDiff ℝ ∞` (smooth, not analytic: `ω` is `⊤` in this Mathlib)
of the map `(a, b) ↦ M_δ(a, b)` on `ℝ × ℝ`; convexity is joint convexity on `ℝ × ℝ`. -/
theorem lemma_4_2 (δ : ℝ) (hδ : 0 < δ) :
    ContDiff ℝ ∞ (fun z : ℝ × ℝ => smoothMax δ z.1 z.2) ∧
    ConvexOn ℝ Set.univ (fun z : ℝ × ℝ => smoothMax δ z.1 z.2) ∧
    (∀ b : ℝ, Monotone (fun a : ℝ => smoothMax δ a b)) ∧
    (∀ a : ℝ, Monotone (fun b : ℝ => smoothMax δ a b)) ∧
    (∀ a b : ℝ, max a b ≤ smoothMax δ a b ∧ smoothMax δ a b ≤ max a b + δ / 2) ∧
    (∀ a b : ℝ, δ ≤ a - b → smoothMax δ a b = a) ∧
    (∀ a b : ℝ, δ ≤ b - a → smoothMax δ a b = b) := by sorry

end MatchedUCLB
