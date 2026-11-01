-- Prove2me | Theorems.Thm_GPHigherGauge_Flatness_commutator_secondOrder
-- name    : GPHigherGauge.Flatness.commutator_secondOrder
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T17:55:47.855674+00:00
-- url     : https://prove2.me/theorems/52d3bb9e-b990-4cfe-9b13-d3a6172fa8cf
-- title:
--   Eq. (3.19) — Baker–Hausdorff to second order, the group commutator of two curves has $a^2$-coefficient $[X,Y]$
-- statement:
--   Let $G$ be a real Lie group with Lie algebra $\mathfrak g$, and let $c_1,c_2:\mathbb R\to G$ be smooth at $0$ with $c_1(0)=c_2(0)=1$ and velocities $X=c_1'(0)$, $Y=c_2'(0)\in\mathfrak g$. Put
--   $$k(a)=c_1(a)\,c_2(a)\,c_1(a)^{-1}\,c_2(a)^{-1}.$$
--   Then $k$ has velocity $0$ at $a=0$, and in the chart $\varphi_1$ of $G$ at the unit
--   $$\frac12\,\frac{d^2}{da^2}\Big|_{a=0}\varphi_1\big(k(a)\big)=[X,Y].$$
--
--   This is the second-order content of the Baker–Hausdorff formula $e^xe^y=e^{x+y+\frac12[x,y]+\cdots}$: for $c_1=e^{aX}$, $c_2=e^{aY}$ it gives $k(a)=e^{a^2[X,Y]+O(a^3)}$. It is the step that produces the bracket term of the curvature $F_{\mu\nu}$.
--
--   Differences from the source:
--   - reading: e^x e^y = e^{x+y+½[x,y]+···} → the group commutator of two curves through 1 has zero velocity and half its second derivative at 0 (chart at 1) is [X, Y]; reason: Mathlib has no Lie-group exponential; this is the second-order content of (3.19), the form used to derive (3.23).
--   - encoding: the Lie bracket [x, y] → Mathlib's GroupLieAlgebra bracket (bracket at 1 of left-invariant vector fields); reason: it is XY − YX on matrix groups, the convention of (3.19) and (3.23).
--   - generalization: finite-dimensional real Lie groups → Lie groups modelled on any real normed space; reason: the finite-dimensional groups of the paper are an instance.
-- source:
--   Girelli, Pfeiffer, Higher gauge theory — differential versus integral formulation, arXiv:hep-th/0309173v2, §3.3, Eq. (3.19), p. 16

import Mathlib

open scoped Manifold ContDiff
open VectorField

namespace GPHigherGauge.Flatness

/-- Baker–Hausdorff to second order, in commutator form: the group commutator of two curves
through `1` has velocity `0`, and its `a²`-coefficient is the Lie bracket of their velocities.

Girelli, Pfeiffer, *Higher gauge theory — differential versus integral formulation*,
arXiv:hep-th/0309173v2, §3.3, Eq. (3.19), p. 16:
"When we have a product of Lie group elements, the Baker–Hausdorff formula allows us to get the
corresponding operation at the Lie algebra level, e^x e^y = e^{x+y+½[x,y]+···}."

Let `G` be a Lie group and `c₁ c₂ : ℝ → G` smooth at `0` with `c₁ 0 = c₂ 0 = 1`, velocities
`X = c₁'(0)`, `Y = c₂'(0)` in `𝔤 = T₁G`. Put `k(a) = c₁(a) c₂(a) c₁(a)⁻¹ c₂(a)⁻¹`. Then `k` has
velocity `0` at `0`, and `½ k''(0)` (in the chart of `G` at `1`) equals `[X, Y]`.

**Formalization Note** Reading 2: Mathlib has no Lie-group exponential, so (3.19) is formalized by
its second-order content, the group-commutator characterization of the bracket (with `c₁ = e^{aX}`,
`c₂ = e^{aY}`, (3.19) gives `k(a) = e^{a²[X,Y] + O(a³)}`); this is the form the computation of
(3.23) uses. The bracket is Mathlib's `GroupLieAlgebra` bracket, written out as in
`GroupLieAlgebra.bracket_def` (Reading 5). -/
theorem commutator_secondOrder {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {G : Type*} [TopologicalSpace G] [ChartedSpace E G] [Group G] [LieGroup 𝓘(ℝ, E) ∞ G]
    (c₁ c₂ : ℝ → G) (hc₁ : ContMDiffAt 𝓘(ℝ, ℝ) 𝓘(ℝ, E) ∞ c₁ 0)
    (hc₂ : ContMDiffAt 𝓘(ℝ, ℝ) 𝓘(ℝ, E) ∞ c₂ 0) (h₁ : c₁ 0 = 1) (h₂ : c₂ 0 = 1) :
    mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (fun a => c₁ a * c₂ a * (c₁ a)⁻¹ * (c₂ a)⁻¹) 0 = 0 ∧
      (1 / 2 : ℝ) • deriv (deriv (fun a =>
          extChartAt 𝓘(ℝ, E) (1 : G) (c₁ a * c₂ a * (c₁ a)⁻¹ * (c₂ a)⁻¹))) 0 =
        mlieBracket 𝓘(ℝ, E)
          (mulInvariantVectorField (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) c₁ 0 1 : GroupLieAlgebra 𝓘(ℝ, E) G))
          (mulInvariantVectorField (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) c₂ 0 1 : GroupLieAlgebra 𝓘(ℝ, E) G))
          (1 : G) := by sorry

end GPHigherGauge.Flatness
