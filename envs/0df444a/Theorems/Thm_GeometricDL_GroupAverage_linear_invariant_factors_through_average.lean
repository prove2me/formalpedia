-- Prove2me | Theorems.Thm_GeometricDL_GroupAverage_linear_invariant_factors_through_average
-- name    : GeometricDL.GroupAverage.linear_invariant_factors_through_average
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-30T03:12:12.15835+00:00
-- url     : https://prove2.me/theorems/6b2cb9a8-d491-4057-81b5-29c22fbfe04b
-- title:
--   A linear $\mathfrak G$-invariant function depends on its input only through the $\mathfrak G$-average
-- statement:
--   Let $\mu$ be a finite, nonzero measure on a group $\mathfrak G$, let $\rho$ be a representation of $\mathfrak G$ by bounded linear operators on a real Banach space $E$ of signals, and let $f : E \to \mathcal Y$ be a continuous linear, $\mathfrak G$-invariant map into a real Banach space $\mathcal Y$. Write
--   $$Ax = \frac{1}{\mu(\mathfrak G)} \int_{\mathfrak G} \rho(\mathfrak g)x \, d\mu(\mathfrak g)$$
--   for the $\mathfrak G$-average. Then:
--
--   1. for every signal $x$ whose orbit $\mathfrak g \mapsto \rho(\mathfrak g)x$ is $\mu$-integrable,
--   $$f(x) = \frac{1}{\mu(\mathfrak G)} \int_{\mathfrak G} f(\rho(\mathfrak g)x)\, d\mu(\mathfrak g) = f\!\left(\frac{1}{\mu(\mathfrak G)} \int_{\mathfrak G} \rho(\mathfrak g)x\, d\mu(\mathfrak g)\right);$$
--   2. for every such $x$, $f(x) = f(Ax)$;
--   3. for all signals $x, y$ with integrable orbits, $Ax = Ay$ implies $f(x) = f(y)$: $f$ depends on $x$ only through its $\mathfrak G$-average.
--
--   This is the observation that opens the blueprint of Geometric Deep Learning (§3.5): linear invariants only see the group average of the input (for images under translation, the average colour), so expressive invariant architectures must compose linear equivariant layers with non-linearities.
--
--   **Formalization Note** $1/\mu(\mathfrak G)$ is `(μ Set.univ).toReal⁻¹` and $\mathfrak g.x$ is `ρ g x`; $A$ is `groupAverage μ ρ`. Integrability is required per signal, not for all signals at once.
--
--   Differences from the source:
--   - reading: f linear → f continuous linear (E →L[ℝ] Y); reason: the display moves f inside a vector-valued integral, which is the property of continuous linear maps; in finite dimension (the paper's grids, side note p. 15) every linear map is continuous
--   - generalization: signals X(Ω) with the action (3) → a real Banach space E with a representation ρ : G →* (E →L[ℝ] E); reason: the paper defines invariance through ρ (p. 15); X(Ω) with (3) over a finite domain is an instance (proved in the sanity file)
--   - reading: µ(G) in the denominator → µ finite and nonzero; reason: the display divides by µ(G); the Haar measure of a compact group is finite and nonzero
--   - reading: "F only depends on x through the G-average" → a statement about f (clauses 2 and 3); reason: F is not otherwise defined in the passage; it refers to the f of the display
--   - generalization: µ the Haar measure of the group → any finite nonzero measure μ; reason: neither equality uses invariance of µ; the Haar case is an instance (sanity file)
--   - encoding: ∫_G (g.x)dµ(g) exists → Integrable (fun g => ρ g x) μ for each signal used; reason: the display presupposes the integral exists; Lean's junk value 0 would otherwise falsify the equalities
--   - encoding: signal and output spaces → E and Y complete; reason: Lean's Bochner integral is 0 in an incomplete space
--   - encoding: 1/µ(G) and g.x → (μ Set.univ).toReal⁻¹ and ρ g x; reason: Lean notation, same quantities
-- source:
--   Bronstein, Bruna, Cohen, Veličković, Geometric Deep Learning: Grids, Groups, Graphs, Geodesics, and Gauges, arXiv:2104.13478v2, §3.5, display on p. 27 (PDF p. 31), both equalities and the G-average sentence that follows; side note on the Haar measure, p. 27

import Mathlib
import Definitions.Def_GeometricDL_GroupAverage_IsGInvariant
import Definitions.Def_GeometricDL_GroupAverage_groupAverage
open MeasureTheory

namespace GeometricDL.GroupAverage

/-- **A linear G-invariant function depends on its input only through the G-average (§3.5, p. 27).**
Bronstein, Bruna, Cohen & Veličković, *Geometric Deep Learning: Grids, Groups, Graphs, Geodesics,
and Gauges*, arXiv:2104.13478v2, §3.5, unnumbered display on printed p. 27 (PDF p. 31): "since if
f is linear and G-invariant, then for all x ∈ X(Ω),
f(x) = (1/µ(G)) ∫_G f(g.x)dµ(g) = f((1/µ(G)) ∫_G (g.x)dµ(g)),
which indicates that F only depends on x through the G-average Ax = (1/µ(G)) ∫_G (g.x)dµ(g)."
Side note: "Here, µ(g) is known as the Haar measure of the group G, and the integral is performed
over the entire group."

Let `μ` be a finite nonzero measure on a group `G`, `ρ : G →* (E →L[ℝ] E)` a representation on a
real Banach space, and `f : E →L[ℝ] Y` a continuous linear G-invariant map into a real Banach
space. Then
1. for every `x` with integrable orbit, both equalities of the display hold;
2. for every `x` with integrable orbit, `f x = f (A x)`, `A = groupAverage μ ρ`;
3. for all `x, y` with integrable orbits, `A x = A y` implies `f x = f y`.

**Formalization Note.** Readings: "f is linear" is continuous linear (R1); the signal space X(Ω)
with the action (3) is an abstract real Banach space with a representation by bounded operators
(R2; the paper's own definition of invariance, p. 15, is phrased with ρ); µ(G) is finite and
positive (R3); "F only depends on x" is about f (R4). Generalization: any finite nonzero measure
in place of the Haar measure (G1). Encodings: the orbit of each signal used is assumed integrable
(E1), `E` and `Y` are complete (E2), since Lean's Bochner integral is `0` otherwise; `1/µ(G)` is
`(μ Set.univ).toReal⁻¹` and `g.x` is `ρ g x` (E3). -/
theorem linear_invariant_factors_through_average {G : Type*} [Group G] [MeasurableSpace G]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y]
    (μ : Measure G) [IsFiniteMeasure μ] [NeZero μ]
    (ρ : G →* (E →L[ℝ] E)) (f : E →L[ℝ] Y) (hf : IsGInvariant ρ f) :
    (∀ x : E, Integrable (fun g => ρ g x) μ →
        f x = (μ Set.univ).toReal⁻¹ • ∫ g, f (ρ g x) ∂μ ∧
        (μ Set.univ).toReal⁻¹ • ∫ g, f (ρ g x) ∂μ =
          f ((μ Set.univ).toReal⁻¹ • ∫ g, ρ g x ∂μ)) ∧
    (∀ x : E, Integrable (fun g => ρ g x) μ → f x = f (groupAverage μ ρ x)) ∧
    (∀ x y : E, Integrable (fun g => ρ g x) μ → Integrable (fun g => ρ g y) μ →
        groupAverage μ ρ x = groupAverage μ ρ y → f x = f y) := by sorry

end GeometricDL.GroupAverage
