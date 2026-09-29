-- Prove2me | Theorems.Thm_NewtonGravitation_gravField_eq_enclosed_mass
-- name    : NewtonGravitation.gravField_eq_enclosed_mass
-- status  : Open
-- author  : @Lucas
-- created : 2026-09-27T18:57:17.314985+00:00
-- url     : https://prove2.me/theorems/ff22e954-f66e-4c93-adf2-25095bc0bc58
-- title:
--   Shell theorem: the field equals that of the enclosed mass at the centre
-- statement:
--   Let $\mu$ be a finite, spherically symmetric mass distribution on $\mathbb{E}^3$ and let $x\in\mathbb{E}^3$ be a point at which the field integrand $y\mapsto -\frac{G}{\|x-y\|^3}(x-y)$ is $\mu$-integrable. Let $M_{<}(x) = \mu(\{y : \|y\|<\|x\|\})$ be the mass enclosed strictly inside the sphere through $x$. Then
--   $$g_\mu(x) = -\frac{G\,M_{<}(x)}{\|x\|^3}\,x .$$
--
--   This combines both bullets of Newton's shell theorem as stated in the source: the mass at radii $r<r_0$ acts as if concentrated at the centre, while the mass at radii $r>r_0$ exerts no net force.
--
--   **Formalization Note** The integrability hypothesis states that the force at $x$ is well defined; without it the Lean integral is $0$ by convention. It excludes, for instance, a uniform shell passing through $x$.
-- source:
--   Wikipedia, "Newton's law of universal gravitation", revision oldid=1370960529 (https://en.wikipedia.org/w/index.php?title=Newton%27s_law_of_universal_gravitation&oldid=1370960529)

import Definitions.Def_NewtonGravitation_Defs
import Mathlib

open MeasureTheory NewtonGravitation

namespace NewtonGravitation

theorem gravField_eq_enclosed_mass (μ : Measure Space) [IsFiniteMeasure μ]
    (hμ : IsSphericallySymmetric μ) (x : Space)
    (hint : Integrable (fun y => -(G / ‖x - y‖ ^ 3) • (x - y)) μ) :
    gravField μ x = pointField (μ.real (Metric.ball 0 ‖x‖)) 0 x := by sorry

end NewtonGravitation
