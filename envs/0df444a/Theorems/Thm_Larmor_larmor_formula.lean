-- Prove2me | Theorems.Thm_Larmor_larmor_formula
-- name    : Larmor.larmor_formula
-- status  : Open
-- author  : @Lucas
-- created : 2026-09-20T01:21:59.390927+00:00
-- url     : https://prove2.me/theorems/4610bb29-7ba7-4c12-8969-ab6767fa50c2
-- title:
--   Larmor formula: $P=\dfrac{q^{2}a^{2}}{6\pi\varepsilon_0c^{3}}=\dfrac{\mu_0q^{2}a^{2}}{6\pi c}$
-- statement:
--   **The Larmor formula.** A point charge $q$ moves along a worldline $w:\mathbb{R}\to\mathbb{R}^3$ that is Lipschitz with a constant $K<c$, so the motion is subluminal. Assume that at time $0$ the charge is at the origin and instantaneously at rest,
--
--   $$w(0)=0,\qquad \dot w(0)=0,$$
--
--   which is the non-relativistic hypothesis under which Larmor's formula is stated, and write $a=\ddot w(0)$ for the acceleration at that instant. Fix a radius $R>0$ and let the observation time $t$ satisfy $c\,t=R$, so the light emitted at time $0$ is exactly reaching the sphere $\|x\|=R$. Let $E$ and $B$ be the Liénard–Wiechert fields of the charge, each evaluated at a retarded time of its observation event. Then the flux of the Poynting vector through that sphere is
--
--   $$\int_{\|x\|=R}\Bigl\langle S(x),\tfrac{x}{R}\Bigr\rangle\,\mathrm d\mathcal H^{2}(x)
--   =\frac{q^{2}\|a\|^{2}}{6\pi\varepsilon_0c^{3}}
--   =\frac{\mu_0q^{2}\|a\|^{2}}{6\pi c},$$
--
--   with $\mu_0=1/(\varepsilon_0c^2)$.
--
--   This is the total power radiated by a non-relativistic accelerating point charge. Three features are worth emphasising. The identity is exact at every finite radius $R>0$, not merely in the limit $R\to\infty$: at the retarded time the charge is at rest, so the velocity part of the field is radial and carries no flux. The answer is independent of $R$, as energy conservation demands for a shell of radiation crossing successive spheres. And it depends on the worldline only through the acceleration at the emission instant, which is the whole content of Larmor's result.
--
--   **Formalization Note** The retarded times are supplied as a function on the observation sphere satisfying the retardation relation; by the mission's uniqueness theorem for subluminal worldlines this function is forced to be identically $0$ on that sphere, so no arbitrary choice is involved. Worldlines satisfying all hypotheses with arbitrary prescribed acceleration $\ddot w(0)$ exist, for example $w(s)=\varepsilon(1-\cos\omega s)\,e$ with $\varepsilon\omega<c$.
-- source:
--   https://en.wikipedia.org/wiki/Larmor_formula — lead formula ("the total power that the particle radiates ... can be calculated by the Larmor formula", SI form $P=\mu_0q^2a^2/(6\pi c)=q^2a^2/(6\pi\varepsilon_0c^3)$) together with the Derivation section; J. D. Jackson, Classical Electrodynamics, 3rd ed., Wiley 1998, eq. (14.22).

import Definitions.Def_Larmor_radiated_power
import Definitions.Def_Larmor_lienard_wiechert

namespace Larmor

theorem larmor_formula (q ε₀ c R t : ℝ) (hε : 0 < ε₀) (hc : 0 < c) (hR : 0 < R) (ht : c * t = R)
    (K : NNReal) (hK : (K : ℝ) < c) (w : ℝ → Vec) (hw : LipschitzWith K w)
    (hw0 : w 0 = 0) (hv0 : deriv w 0 = 0)
    (tr : Vec → ℝ) (htr : ∀ x ∈ Metric.sphere (0 : Vec) R, IsRetardedTime c w t x (tr x)) :
    radiatedFlux ε₀ c (fun x => lwE q ε₀ c w (tr x) x) (fun x => lwB q ε₀ c w (tr x) x) R
      = q ^ 2 * ‖deriv (deriv w) 0‖ ^ 2 / (6 * Real.pi * ε₀ * c ^ 3) := by sorry

end Larmor
