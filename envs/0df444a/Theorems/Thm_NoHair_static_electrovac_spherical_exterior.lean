-- Prove2me | Theorems.Thm_NoHair_static_electrovac_spherical_exterior
-- name    : NoHair.static_electrovac_spherical_exterior
-- status  : Open
-- author  : @Igor Valuev
-- created : 2026-11-22T20:52:26.922809+00:00
-- url     : https://prove2.me/theorems/83ad6c96-9e03-4d9c-af33-a3604eb80469
-- title:
--   Global spherical areal coordinates for a static electrovacuum black hole
-- statement:
--   Consider a smooth time-oriented stationary electrovacuum spacetime with an asymptotically flat end adapted to its symmetry flow. Assume its domain of outer communications $D$ is globally hyperbolic, the black-hole region is nonempty, the future event horizon is connected, and the generator of the flow is hypersurface-orthogonal on $D$.
--
--   The entire domain $D$ admits a spherical areal chart with inner radius $R>0$. With $k=dt+dr$ and $B=d(k/r)$, its metric and electromagnetic field have the form
--
--   $$
--   g=\eta+(1-A(r))k\otimes k,\qquad F=q(r)B+p(r)\star_g B.
--   $$
--
--   The squared lapse $A$ is positive outside $R$ and extends continuously to zero at $R$. This is the global rigidity step of the static electrovacuum uniqueness argument. A proof from the milestone's hypotheses must justify the topology and coverage of the spherical chart, including the case of a degenerate horizon.
--
--   **Status of the global rigidity claim.** The equal-mass two-centre Majumdar–Papapetrou spacetime can be extended across one future horizon while the second extremal throat remains an open end. The frontier of the exterior relative to that spacetime is a single connected cylinder. The two-centre exterior has both zero and nonzero Faraday tensors at regular points. The positive static classification of Chruściel and Tod controls the interior ends through a compact-interior hypothesis on a spacelike hypersurface. The present milestone does not impose it. The parent sketch records the counterexample and the remaining steps in a machine-checked disproof. [Parent theorem](https://prove2.me/theorems/ae80f2c5-e7b6-4f5e-ab99-ed248fa30fca) · [Connected frontier](https://prove2.me/theorems/0de0590b-43e7-4842-bb91-2326e3abdd84) · [Field obstruction](https://prove2.me/theorems/8dd49003-60bb-49a3-ae6d-a0ae29895f25) · [Chruściel and Tod, Theorem 1.1](https://arxiv.org/abs/gr-qc/0512043)
--
--   The explicit spacetime and the open obligations in its formal construction can be inspected together. [Counterexample proof sketch](https://prove2.me/theorems/84975594-a830-42db-a289-c13d23e1c01b)
-- source:
--   W. Israel, Event horizons in static electrovac space-times, Commun. Math. Phys. 8 (1968), 245–260, https://doi.org/10.1007/BF01645859. P. T. Chruściel and P. Tod, The classification of static electro-vacuum space-times containing an asymptotically flat spacelike hypersurface with compact interior, Theorem 1.1(i), https://arxiv.org/abs/gr-qc/0512043. Global chart subproblem for NoHair.israel_static_electrovac in its stated hypotheses.

import Definitions.Def_NoHair_sphericalArealExterior

open scoped ContDiff Manifold

theorem NoHair.static_electrovac_spherical_exterior {M : Type*}
    [TopologicalSpace M] [ChartedSpace NoHair.E4 M] [IsManifold 𝓘(ℝ, NoHair.E4) ∞ M]
    (g F : NoHair.BilinField M) (T : NoHair.VecField M) (φ : ℝ → M → M)
    (E : NoHair.AsymptoticallyFlatEnd g F φ) (h : NoHair.IsStationaryBlackHole g F T φ E)
    (hstatic : NoHair.IsStaticOn g φ (NoHair.domainOfOuterCommunications g T E.region)) :
    Nonempty (NoHair.SphericalArealExterior g F (NoHair.domainOfOuterCommunications g T E.region)) := by
  sorry
