-- Prove2me | Theorems.Thm_NoHair_static_vacuum_spherical_chart
-- name    : NoHair.static_vacuum_spherical_chart
-- status  : Open
-- author  : @Igor Valuev
-- created : 2026-11-22T21:08:14.43557+00:00
-- url     : https://prove2.me/theorems/ff7cb3e1-34b3-46ba-bc3b-0e48276ce41b
-- title:
--   Global spherical chart for a static vacuum black-hole exterior
-- statement:
--   Consider the static vacuum black hole of the 1967 milestone. Its electromagnetic field vanishes everywhere. Its asymptotic end determines the domain of outer communications $D$.
--
--   The geometric problem is to construct a global spherical areal chart of $D$ with horizon radius $R>0$ and squared lapse $A(r)$. In particular $A$ extends continuously to $A(R)=0$. In the exterior $A$ is differentiable. In ingoing time $v$ and local angular coordinates $z=\cos\theta,\varphi$, the metric reads
--   $$
--   G=-A(r)\,dv^2+2\,dv\,dr+r^2\left(\frac{dz^2}{1-z^2}+(1-z^2)\,d\varphi^2\right).
--   $$
--   For each $r>R$ the angular vacuum equation $\operatorname{Ric}(G)_{\varphi\varphi}=0$ holds at $v=z=\varphi=0$. This last requirement expresses the vacuum field equation in the displayed coordinates using the platform's Ricci tensor. Establishing the global chart from the stated spacetime assumptions is the spherical rigidity step of Israel's theorem.
-- source:
--   Geometric subproblem of Israel (1967), https://prove2.me/theorems/1931bf7b-9b31-4f01-9a4c-3563c9cdbf9a. W. Israel, Event Horizons in Static Vacuum Space-Times, Phys. Rev. 164 (1967), pp. 1776–1779, https://doi.org/10.1103/PhysRev.164.1776. Global hypotheses used to obtain a spherical chart must be justified for the mission statement.

import Definitions.Def_NoHair_sphericalArealExterior

open scoped ContDiff Manifold
open Set NoHair

theorem NoHair.static_vacuum_spherical_chart {M : Type*} [TopologicalSpace M]
    [ChartedSpace E4 M] [IsManifold 𝓘(ℝ, E4) ∞ M] (g F : BilinField M) (T : VecField M)
    (φ : ℝ → M → M) (E : AsymptoticallyFlatEnd g F φ) (h : IsStationaryBlackHole g F T φ E)
    (hvac : ∀ x, F x = 0)
    (hstatic : IsStaticOn g φ (domainOfOuterCommunications g T E.region)) :
    ∃ S : SphericalArealExterior g F (domainOfOuterCommunications g T E.region),
      (∀ r, S.horizonRadius < r → DifferentiableAt ℝ S.lapseSq r) ∧
      ∀ r, S.horizonRadius < r →
        let G := fun y : E4 => !![-S.lapseSq (y 1), 1, 0, 0;
          1, 0, 0, 0; 0, 0, y 1 ^ 2 / (1 - y 2 ^ 2), 0;
          0, 0, 0, y 1 ^ 2 * (1 - y 2 ^ 2)]
        ricci G (WithLp.toLp 2 ![0, r, 0, 0]) 3 3 = 0 := by sorry
