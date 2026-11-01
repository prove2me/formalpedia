-- Prove2me | Theorems.Thm_GPHigherGauge_Flatness_levelOne_flatness
-- name    : GPHigherGauge.Flatness.levelOne_flatness
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T17:57:14.127027+00:00
-- url     : https://prove2.me/theorems/dcc8cc41-55cf-48b7-aebe-e3c76a79cf4b
-- title:
--   Eq. (3.25) — level-1 flatness $\tau(B)=-F$ of the 2-connection of smoothly varying crossed-module labels
-- statement:
--   Let $(t,\triangleright)$ be a smooth crossed module of real Lie groups: $t:H\to G$ a smooth homomorphism and $\triangleright$ a smooth action of $G$ on $H$ by automorphisms with $t(g\triangleright h)=g\,t(h)\,g^{-1}$ and $t(h)\triangleright h'=hh'h^{-1}$. Let $\tau=dt_1:\mathfrak h\to\mathfrak g$.
--
--   On $\mathbb R^n$ with unit vectors $e_\mu$, let $g_\mu(x,a)\in G$ label the edge from $x$ to $x+ae_\mu$ and $h_{\mu\nu}(x,a)\in H$ label the square at $x$ with sides $ae_\mu$, $ae_\nu$. Fix $x_0\in\mathbb R^n$ and assume:
--   1. the labels are $C^\infty$ in $(x,a)$ near $(x_0,0)$, with $g_\mu(x,0)=1$ for $x$ near $x_0$, $h_{\mu\nu}(x_0,0)=1$ and $\partial_ah_{\mu\nu}(x_0,0)=0$ for $\mu\neq\nu$;
--   2. every small square near $(x_0,0)$ satisfies the surface condition
--   $$t\big(h_{\mu\nu}(x,a)\big)=\big(g_\nu(x,a)\,g_\mu(x+ae_\nu,a)\big)\big(g_\mu(x,a)\,g_\nu(x+ae_\mu,a)\big)^{-1}\qquad(\mu\neq\nu).$$
--
--   Let $A_\mu(x)=\partial_a g_\mu(x,a)|_{a=0}$ and $B_{\mu\nu}(x_0)=\tfrac12\partial_a^2h_{\mu\nu}(x_0,a)|_{a=0}$ be the connection 1- and 2-forms. Then for all $\mu\neq\nu$
--   $$\tau\big(B_{\mu\nu}(x_0)\big)=-\Big(\partial_\mu A_\nu(x_0)-\partial_\nu A_\mu(x_0)+[A_\mu(x_0),A_\nu(x_0)]\Big)=-F_{\mu\nu}(x_0).$$
--
--   Equivalently, the fake curvature $\widetilde F=F+\tau(B)$ of the 2-connection $(A,B)$ vanishes: in the differential formulation of 2-gauge theory, the integral picture's surface condition forces level-1 flatness. This is the condition that the paper finds has "drastic consequences".
--
--   Differences from the source:
--   - reading: all labels depend smoothly on the curves and surfaces → (x, a) ↦ g_μ(x, a) and (x, a) ↦ h_μν(x, a) are C^∞ near (x₀, 0), and the surface condition holds for a of either sign; reason: the derivation uses only axis-parallel edges and squares at the base point; the square with side a < 0 is also a surface of the configuration.
--   - reading: g_μ ∼ e^{aA_μ}, h_μν ∼ e^{a²B_μν} (3.16) → g_μ(x, 0) = 1 near x₀, h_μν(x₀, 0) = 1, ∂_a h_μν(x₀, 0) = 0, A_μ the a-derivative of g_μ and B_μν half the second a-derivative of h_μν at a = 0 in the chart at 1; reason: Mathlib has no Lie-group exponential.
--   - generalization: a configuration on a coordinate patch → hypotheses only near (x₀, 0) and the conclusion at x₀; reason: a configuration on a patch containing x₀ satisfies these hypotheses at each of its points.
--   - generalization: a full configuration of 2-gauge theory → only the straight edges and the squares with (2.10) (h_μν = h_νμ⁻¹ not assumed); reason: every configuration supplies these labels.
--   - encoding: the Lie bracket [A_μ, A_ν] → Mathlib's GroupLieAlgebra bracket (bracket at 1 of left-invariant vector fields); reason: it is XY − YX on matrix groups, the convention of (3.19) and (3.23).
--   - generalization: finite-dimensional real Lie groups → Lie groups modelled on any real normed space; reason: the finite-dimensional groups of the paper are an instance.
-- source:
--   Girelli, Pfeiffer, Higher gauge theory — differential versus integral formulation, arXiv:hep-th/0309173v2, §3.3, Eq. (3.25), p. 17 (with F from Eq. (3.23), p. 16, and Eqs. (2.10), p. 6, (3.16), p. 15)

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P15
import Definitions.Def_GPHigherGauge_Flatness_connectionTwoForm
import Definitions.Def_GPHigherGauge_Flatness_tau
import Definitions.Def_GPHigherGauge_Flatness_curvature
import Definitions.Def_GPHigherGauge_Flatness_IsSmoothSquareLabels
import Definitions.Def_GPHigherGauge_Flatness_SurfaceCondition

open scoped Manifold ContDiff
open QAlgorithms.Papers.Independent.Intake100.P15

namespace GPHigherGauge.Flatness

/-- Level-1 flatness: smoothly varying curve and surface labels of a Lie crossed module force
`τ(B) = −F`.

Girelli, Pfeiffer, *Higher gauge theory — differential versus integral formulation*,
arXiv:hep-th/0309173v2, §3.3, Eq. (3.25), p. 17:
"It is important here to remember that in the definition of a strict Lie 2-group, we have
𝓕 = 1 ∈ H in (2.37) and therefore at the differential level, τ(B) = −F. (3.25) This condition is
the alter ego of the equations (2.10) and (3.8) and has some drastic consequences: it means that the
curvature 2-form F̃ is always zero." (`F` is the conventional curvature of (3.23), p. 16.)

Let `(t, ▷)` be a smooth crossed module of real Lie groups `G`, `H` (§2.1, p. 5). Let `g μ x a` be
the label of the edge from `x` to `x + a e_μ` and `h μ ν x a` the label of the square at `x` with
sides `a e_μ`, `a e_ν` (Figure 1(c)), smooth near `(x₀, 0)` with the infinitesimal form (3.16)
(`IsSmoothSquareLabels`), and satisfying the surface condition (2.10) on every small square near
`(x₀, 0)` (`SurfaceCondition`). Then for all `μ ≠ ν`
`τ(B_μν(x₀)) = −(∂_μA_ν(x₀) − ∂_νA_μ(x₀) + [A_μ(x₀), A_ν(x₀)])`,
equivalently the fake curvature `F̃_μν(x₀) = F_μν(x₀) + τ(B_μν(x₀))` vanishes.

**Formalization Note** `A = connectionOneForm g`, `B = connectionTwoForm h`, `τ = tau t`,
`F = curvature g`. The page's "𝓕 = 1 ∈ H" is a slip for "∈ G" ((2.37) "always gives the group unit
of G"). Readings 1–7 of the mission: smoothness as `C^∞` in `(x, a)` near `(x₀, 0)`, `a` of either
sign; (3.16) as derivatives at `a = 0`; local data with a pointwise conclusion; only edges and
squares; Mathlib's `GroupLieAlgebra` bracket; Lie groups modelled on any real normed space; the
action `▷` (`alpha`) carried as in the paper. -/
theorem levelOne_flatness {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {G : Type*} [TopologicalSpace G] [ChartedSpace E G] [Group G] [LieGroup 𝓘(ℝ, E) ∞ G]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {H : Type*} [TopologicalSpace H] [ChartedSpace F H] [Group H] [LieGroup 𝓘(ℝ, F) ∞ H]
    {n : ℕ} (t : H → G) (alpha : G × H → H)
    (hX : IsSmoothCrossedModule (E := E) (F := F) t alpha)
    (g : Fin n → EuclideanSpace ℝ (Fin n) → ℝ → G)
    (h : Fin n → Fin n → EuclideanSpace ℝ (Fin n) → ℝ → H) (x₀ : EuclideanSpace ℝ (Fin n))
    (hgh : IsSmoothSquareLabels (E := E) (F := F) g h x₀) (hsurf : SurfaceCondition t g h x₀)
    (μ ν : Fin n) (hμν : μ ≠ ν) :
    tau (E := E) (F := F) t (connectionTwoForm h μ ν x₀) = -curvature (E := E) g μ ν x₀ := by sorry

end GPHigherGauge.Flatness
