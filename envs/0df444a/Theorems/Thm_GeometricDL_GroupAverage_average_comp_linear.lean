-- Prove2me | Theorems.Thm_GeometricDL_GroupAverage_average_comp_linear
-- name    : GeometricDL.GroupAverage.average_comp_linear
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-30T03:11:32.569445+00:00
-- url     : https://prove2.me/theorems/92c3f2f0-b8d7-4951-903c-5b25835b8376
-- title:
--   A linear map commutes with the group average
-- statement:
--   Let $\mu$ be a measure on a group $\mathfrak G$, let $\rho$ be a representation of $\mathfrak G$ by bounded linear operators on a real Banach space $E$, and let $f : E \to \mathcal Y$ be a continuous linear map into a real Banach space $\mathcal Y$. If the orbit $\mathfrak g \mapsto \rho(\mathfrak g)x$ of a signal $x \in E$ is $\mu$-integrable, then
--   $$\frac{1}{\mu(\mathfrak G)} \int_{\mathfrak G} f(\rho(\mathfrak g)x)\, d\mu(\mathfrak g) = f\!\left(\frac{1}{\mu(\mathfrak G)} \int_{\mathfrak G} \rho(\mathfrak g)x \, d\mu(\mathfrak g)\right).$$
--
--   This is the second equality of the display in §3.5 of the paper: a linear map can be moved outside the normalised integral over the group.
--
--   **Formalization Note** $1/\mu(\mathfrak G)$ is `(μ Set.univ).toReal⁻¹`, which is $0$ when $\mu(\mathfrak G) = \infty$; both sides are then $0$.
--
--   Differences from the source:
--   - reading: f linear → f continuous linear (E →L[ℝ] Y); reason: the step moves f inside a vector-valued integral, which is the property of continuous linear maps; in finite dimension (the paper's grids, side note p. 15) every linear map is continuous
--   - generalization: µ the Haar measure of the group (finite, nonzero) → any measure μ; reason: the equality uses neither invariance nor finiteness of µ; the paper's measure is an instance
--   - generalization: f linear and G-invariant → f any continuous linear map; reason: the second equality uses only linearity
--   - generalization: signals X(Ω) with the action (3) → a real Banach space E with a representation ρ : G →* (E →L[ℝ] E); reason: the paper defines invariance through ρ (p. 15); X(Ω) with (3) over a finite domain is an instance
--   - encoding: ∫_G (g.x)dµ(g) exists → Integrable (fun g => ρ g x) μ; reason: the display presupposes the integral exists; Lean's junk value 0 would otherwise falsify it
--   - encoding: signal and output spaces → E and Y complete; reason: Lean's Bochner integral is 0 in an incomplete space
--   - encoding: 1/µ(G) and g.x → (μ Set.univ).toReal⁻¹ and ρ g x; reason: Lean notation, same quantities
-- source:
--   Bronstein, Bruna, Cohen, Veličković, Geometric Deep Learning: Grids, Groups, Graphs, Geodesics, and Gauges, arXiv:2104.13478v2, §3.5, display on p. 27 (PDF p. 31), second equality

import Mathlib
open MeasureTheory

namespace GeometricDL.GroupAverage

/-- **Second equality of the §3.5 display: (1/µ(G)) ∫_G f(g.x) dµ(g) = f((1/µ(G)) ∫_G (g.x) dµ(g))
(p. 27).**
Bronstein, Bruna, Cohen & Veličković, *Geometric Deep Learning: Grids, Groups, Graphs, Geodesics,
and Gauges*, arXiv:2104.13478v2, §3.5, unnumbered display on printed p. 27 (PDF p. 31), second
equality: "(1/µ(G)) ∫_G f(g.x)dµ(g) = f((1/µ(G)) ∫_G (g.x)dµ(g))", stated there for f linear.

For any measure `μ` on a group `G`, a representation `ρ : G →* (E →L[ℝ] E)` on a real Banach space,
a continuous linear map `f : E →L[ℝ] Y` into a real Banach space and a signal `x` whose orbit
`g ↦ ρ g x` is `μ`-integrable,
`(μ G)⁻¹ • ∫ g, f (ρ g x) ∂μ = f ((μ G)⁻¹ • ∫ g, ρ g x ∂μ)`.

**Formalization Note.** Reading: "f is linear" is read as continuous linear (`E →L[ℝ] Y`), the
class of maps that commute with a vector-valued integral; in finite dimension every linear map is
continuous. Generalizations: `f` need not be G-invariant, and `μ` is any measure (the paper's is a
Haar measure of finite total mass; for `μ G = ∞` both sides are `0`). Encodings: the orbit of `x`
is assumed integrable, since the display presupposes that `∫_G (g.x) dµ(g)` exists (Lean's junk
value `0` would otherwise falsify it); `E` and `Y` are complete, for the same reason; `1/µ(G)` is
`(μ Set.univ).toReal⁻¹`, `g.x` is `ρ g x`. -/
theorem average_comp_linear {G : Type*} [Group G] [MeasurableSpace G]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y]
    (μ : Measure G) (ρ : G →* (E →L[ℝ] E)) (f : E →L[ℝ] Y) (x : E)
    (hx : Integrable (fun g => ρ g x) μ) :
    (μ Set.univ).toReal⁻¹ • ∫ g, f (ρ g x) ∂μ = f ((μ Set.univ).toReal⁻¹ • ∫ g, ρ g x ∂μ) := by sorry

end GeometricDL.GroupAverage
