-- Prove2me | Theorems.Thm_GeometricDL_GroupAverage_invariant_eq_average_of_orbit
-- name    : GeometricDL.GroupAverage.invariant_eq_average_of_orbit
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-30T03:11:12.550619+00:00
-- url     : https://prove2.me/theorems/1b3e17a1-0a8e-475b-a0ac-0f92dea91420
-- title:
--   An invariant function equals its average over the orbit
-- statement:
--   Let $\mu$ be a finite, nonzero measure on a group $\mathfrak G$, let $\rho$ be a representation of $\mathfrak G$ by bounded linear operators on a real normed space $E$, and let $f : E \to \mathcal Y$ be a $\mathfrak G$-invariant function into a real Banach space $\mathcal Y$. Then for every signal $x \in E$,
--   $$f(x) = \frac{1}{\mu(\mathfrak G)} \int_{\mathfrak G} f(\rho(\mathfrak g)x)\, d\mu(\mathfrak g).$$
--
--   This is the first equality of the display in §3.5 of the paper: by invariance the integrand is constant along the orbit, so the normalised integral returns $f(x)$.
--
--   **Formalization Note** $1/\mu(\mathfrak G)$ is `(μ Set.univ).toReal⁻¹`; $\mathcal Y$ is complete because Lean's Bochner integral is $0$ in an incomplete space.
--
--   Differences from the source:
--   - generalization: µ the Haar measure of the group → any finite nonzero measure μ; reason: the equality does not use invariance of µ; a Haar measure of a compact group is finite and nonzero, so the paper's case is an instance
--   - generalization: f linear and G-invariant → f any G-invariant function; reason: the first equality uses only invariance; linear invariant maps are instances
--   - generalization: signals X(Ω) with the action (3) → a real normed space E with a representation ρ : G →* (E →L[ℝ] E); reason: the paper defines invariance through ρ (p. 15); X(Ω) with (3) over a finite domain is an instance (proved in the sanity file)
--   - reading: µ(G) in the denominator → µ finite and nonzero; reason: the display divides by µ(G)
--   - encoding: values of f in a space Y → Y a real Banach space; reason: Lean's Bochner integral is 0 in an incomplete space; the paper's outputs are finite-dimensional
--   - encoding: 1/µ(G) and g.x → (μ Set.univ).toReal⁻¹ and ρ g x; reason: Lean notation, same quantities
-- source:
--   Bronstein, Bruna, Cohen, Veličković, Geometric Deep Learning: Grids, Groups, Graphs, Geodesics, and Gauges, arXiv:2104.13478v2, §3.5, display on p. 27 (PDF p. 31), first equality

import Mathlib
import Definitions.Def_GeometricDL_GroupAverage_IsGInvariant
open MeasureTheory

namespace GeometricDL.GroupAverage

/-- **First equality of the §3.5 display: f(x) = (1/µ(G)) ∫_G f(g.x) dµ(g) (p. 27).**
Bronstein, Bruna, Cohen & Veličković, *Geometric Deep Learning: Grids, Groups, Graphs, Geodesics,
and Gauges*, arXiv:2104.13478v2, §3.5, unnumbered display on printed p. 27 (PDF p. 31), first
equality: "if f is linear and G-invariant, then for all x ∈ X(Ω), f(x) = (1/µ(G)) ∫_G f(g.x)dµ(g)".

For a finite nonzero measure `μ` on a group `G`, a representation `ρ : G →* (E →L[ℝ] E)` on a real
normed space and a G-invariant function `f : E → Y` into a real Banach space, every signal `x`
satisfies `f x = (μ G)⁻¹ • ∫ g, f (ρ g x) ∂μ`.

**Formalization Note.** Generalizations: `μ` is any finite nonzero measure (the paper's is the
Haar measure of a compact group, which is one); `f` need not be linear (the first equality uses
only invariance). Readings: µ(G) is finite and positive, since the display divides by it.
Encoding: `Y` is complete, since Lean's Bochner integral is `0` in an incomplete space; `1/µ(G)`
is `(μ Set.univ).toReal⁻¹`, `g.x` is `ρ g x`. No integrability hypothesis is needed: the
integrand is constant. -/
theorem invariant_eq_average_of_orbit {G : Type*} [Group G] [MeasurableSpace G]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y]
    (μ : Measure G) [IsFiniteMeasure μ] [NeZero μ]
    (ρ : G →* (E →L[ℝ] E)) (f : E → Y) (hf : IsGInvariant ρ f) (x : E) :
    f x = (μ Set.univ).toReal⁻¹ • ∫ g, f (ρ g x) ∂μ := by sorry

end GeometricDL.GroupAverage
