-- Prove2me | Theorems.Thm_GPHigherGauge_Flatness_generalizedHolonomy_secondOrder
-- name    : GPHigherGauge.Flatness.generalizedHolonomy_secondOrder
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T17:58:08.690852+00:00
-- url     : https://prove2.me/theorems/3d86aa49-72ea-4f97-8b69-ad9910f56ef1
-- title:
--   Eqs. (3.22)–(3.23) — the generalized holonomy of a small square expands to $e^{a^2\widetilde F_{\mu\nu}}$
-- statement:
--   Let $(t,\triangleright)$ be a smooth crossed module of real Lie groups $G,H$ with $\tau=dt_1$. Let $g_\mu(x,a)$ be the labels of the edges from $x$ to $x+ae_\mu$ and $h_{\mu\nu}(x,a)$ the labels of the squares at $x$ with sides $ae_\mu,ae_\nu$, smooth near $(x_0,0)$ with $g_\mu(x,0)=1$ near $x_0$, $h_{\mu\nu}(x_0,0)=1$ and $\partial_ah_{\mu\nu}(x_0,0)=0$; let $A_\mu$, $B_{\mu\nu}$ be the connection 1- and 2-forms, $F_{\mu\nu}$ the curvature of $A$, and
--   $$\mathcal F_{\mu\nu}(x_0,a)=g_\mu(x_0+ae_\nu,a)^{-1}g_\nu(x_0,a)^{-1}\,t\big(h_{\mu\nu}(x_0,a)\big)\,g_\mu(x_0,a)\,g_\nu(x_0+ae_\mu,a)$$
--   the generalized holonomy of the square. The surface condition is not assumed. Then for $\mu\neq\nu$ the curve $a\mapsto\mathcal F_{\mu\nu}(x_0,a)$ has velocity $0$ at $a=0$ and, in the chart $\varphi_1$ of $G$ at the unit,
--   $$\frac12\,\frac{d^2}{da^2}\Big|_{a=0}\varphi_1\big(\mathcal F_{\mu\nu}(x_0,a)\big)=\widetilde F_{\mu\nu}(x_0)=\partial_\mu A_\nu-\partial_\nu A_\mu+[A_\mu,A_\nu]+\tau(B_{\mu\nu}).$$
--
--   That is, $\mathcal F_{\mu\nu}\sim e^{a^2\widetilde F_{\mu\nu}}$ up to terms of order $a^3$: the fake curvature $\widetilde F=F+\tau(B)$ is the curvature read off the holonomy of an infinitesimal square in 2-gauge theory.
--
--   Differences from the source:
--   - reading: e^{a²F̃_μν} ∼ 𝓕_μν, dropping all terms of order a³ in the exponent → 𝓕_μν(x₀, ·) has zero velocity at a = 0 and half its second derivative there (chart of G at 1) equals F̃_μν(x₀); reason: Mathlib has no Lie-group exponential; this is the exact content of the second-order expansion.
--   - reading: all labels depend smoothly on the curves and surfaces → (x, a) ↦ g_μ(x, a) and (x, a) ↦ h_μν(x, a) are C^∞ near (x₀, 0), with a of either sign; reason: the derivation uses only axis-parallel edges and squares at the base point.
--   - reading: g_μ ∼ e^{aA_μ}, h_μν ∼ e^{a²B_μν} (3.16) → g_μ(x, 0) = 1 near x₀, h_μν(x₀, 0) = 1, ∂_a h_μν(x₀, 0) = 0, A_μ the a-derivative of g_μ and B_μν half the second a-derivative of h_μν at a = 0; reason: Mathlib has no Lie-group exponential.
--   - generalization: a configuration on a coordinate patch → hypotheses only near (x₀, 0) and the conclusion at x₀; reason: a configuration on a patch containing x₀ satisfies these hypotheses.
--   - generalization: a full configuration of 2-gauge theory → only the straight edges and the squares (h_μν = h_νμ⁻¹ not assumed); reason: every configuration supplies these labels.
--   - encoding: the Lie bracket [A_μ, A_ν] → Mathlib's GroupLieAlgebra bracket; reason: it is XY − YX on matrix groups, the convention of (3.19) and (3.23).
--   - generalization: finite-dimensional real Lie groups → Lie groups modelled on any real normed space; reason: the finite-dimensional groups of the paper are an instance.
-- source:
--   Girelli, Pfeiffer, Higher gauge theory — differential versus integral formulation, arXiv:hep-th/0309173v2, §3.3, Eqs. (3.22)–(3.23), p. 16; Eq. (3.16) and Figure 1(c), p. 15

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P15
import Definitions.Def_GPHigherGauge_Flatness_fakeCurvature
import Definitions.Def_GPHigherGauge_Flatness_generalizedHolonomy
import Definitions.Def_GPHigherGauge_Flatness_IsSmoothSquareLabels

open scoped Manifold ContDiff
open QAlgorithms.Papers.Independent.Intake100.P15

namespace GPHigherGauge.Flatness

/-- Expansion of the generalized holonomy of a small square to second order: its `a²`-coefficient
is the fake curvature `F̃_μν = ∂_μA_ν − ∂_νA_μ + [A_μ, A_ν] + τ(B_μν)`.

Girelli, Pfeiffer, *Higher gauge theory — differential versus integral formulation*,
arXiv:hep-th/0309173v2, §3.3, Eqs. (3.22)–(3.23), p. 16:
"The expression 𝓕 of (2.37) reads for the square of Figure 1(c), e^{a²F̃_µν} ∼ 𝓕_µν =
g_µ^{-1}(ν) g_ν(0)^{-1} t(h_µν(0)) g_µ(0) g_ν(µ). (3.22) Using the approximations (3.16–3.19) and
dropping all terms of order a³ in the exponent, we obtain the curvature 2-form F̃_µν = ½ F̃_µν
dx^µ ∧ dx^ν as follows, F̃_µν = ∂_µA_ν − ∂_νA_µ + [A_µ, A_ν] + τ(B_µν) = F_µν + τ(B_µν), (3.23)
where F denotes the conventional curvature of A."

Let `(t, ▷)` be a smooth crossed module of real Lie groups `G`, `H`, and let the edge labels `g`
and square labels `h` be smooth near `(x₀, 0)` with the infinitesimal form (3.16)
(`IsSmoothSquareLabels`). The surface condition (2.10) is **not** assumed. Then for `μ ≠ ν` the
curve `a ↦ 𝓕_μν(x₀, a)` has velocity `0` at `a = 0`, and `½ · d²/da² 𝓕_μν(x₀, a)|_{a=0}` (in the
chart of `G` at `1`) equals `F̃_μν(x₀)`.

**Formalization Note** "e^{a²F̃} ∼ 𝓕, dropping terms of order a³" is read as: zero first
derivative and `F̃` = half the second derivative at `a = 0` (Reading 2). Readings 1–7 of the
mission apply. -/
theorem generalizedHolonomy_secondOrder {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {G : Type*} [TopologicalSpace G] [ChartedSpace E G] [Group G] [LieGroup 𝓘(ℝ, E) ∞ G]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {H : Type*} [TopologicalSpace H] [ChartedSpace F H] [Group H] [LieGroup 𝓘(ℝ, F) ∞ H]
    {n : ℕ} (t : H → G) (alpha : G × H → H)
    (hX : IsSmoothCrossedModule (E := E) (F := F) t alpha)
    (g : Fin n → EuclideanSpace ℝ (Fin n) → ℝ → G)
    (h : Fin n → Fin n → EuclideanSpace ℝ (Fin n) → ℝ → H) (x₀ : EuclideanSpace ℝ (Fin n))
    (hgh : IsSmoothSquareLabels (E := E) (F := F) g h x₀) (μ ν : Fin n) (hμν : μ ≠ ν) :
    mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (fun a => generalizedHolonomy t g h μ ν x₀ a) 0 = 0 ∧
      (1 / 2 : ℝ) • deriv (deriv (fun a =>
          extChartAt 𝓘(ℝ, E) (1 : G) (generalizedHolonomy t g h μ ν x₀ a))) 0 =
        fakeCurvature (E := E) (F := F) t g h μ ν x₀ := by sorry

end GPHigherGauge.Flatness
