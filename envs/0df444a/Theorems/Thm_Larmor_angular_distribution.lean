-- Prove2me | Theorems.Thm_Larmor_angular_distribution
-- name    : Larmor.angular_distribution
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-20T01:21:03.040987+00:00
-- url     : https://prove2.me/theorems/1193a267-d554-42d8-904c-6823711a3947
-- title:
--   Angular distribution: $\mathrm dP/\mathrm d\Omega=q^2a^2\sin^2\theta/(16\pi^2\varepsilon_0c^3)$
-- statement:
--   **Angular distribution of radiated power.** Let $\varepsilon_0>0$, $c>0$ and $R>0$, and let a point charge $q$ move along a worldline $w$ with
--
--   $$w(0)=0,\qquad \dot w(0)=0,$$
--
--   so that at time $0$ the charge is at the origin and instantaneously at rest — the non-relativistic situation. Write $a=\ddot w(0)$ for its acceleration at that instant. Let $E$ and $B$ be the Liénard–Wiechert fields evaluated at the retarded time $0$. Then at every observation point $x$ with $\|x\|=R$, with outward unit normal $n=x/R$,
--
--   $$\bigl\langle S(x),n\bigr\rangle=\frac{q^{2}\bigl(\|a\|^{2}-\langle a,n\rangle^{2}\bigr)}{16\pi^{2}\varepsilon_0c^{3}R^{2}}
--   =\frac{q^{2}a^{2}\sin^{2}\theta}{16\pi^{2}\varepsilon_0c^{3}R^{2}},$$
--
--   where $\theta$ is the angle between the acceleration and the direction of observation. Equivalently, the power per unit solid angle is $\mathrm dP/\mathrm d\Omega=R^2\langle S,n\rangle=q^2a^2\sin^2\theta/(16\pi^2\varepsilon_0c^3)$: the characteristic $\sin^2\theta$ doughnut pattern, with no radiation along the direction of the acceleration and a maximum perpendicular to it.
--
--   Two features of the exact field enter. The velocity ("Coulomb") term of the Liénard–Wiechert field is radial when the charge is at rest and therefore contributes nothing to the flux, and the radiation term is transverse with magnitude $q\|n\times(n\times a)\|/(4\pi\varepsilon_0c^2R)$, whose square gives the stated numerator through $\|n\times(n\times a)\|^2=\|a\|^2-\langle a,n\rangle^2$.
--
--   **Formalization Note** The statement is an exact identity at finite radius $R$; no far-field approximation is taken. The distance appearing in the Liénard–Wiechert fields coincides with $R$ because $w(0)=0$ and $\|x\|=R$.
-- source:
--   https://en.wikipedia.org/wiki/Larmor_formula — Angular distribution section (CGS form; the SI form differs by the factor $1/(4\pi\varepsilon_0)$), specialised to $\beta=0$; J. D. Jackson, Classical Electrodynamics, 3rd ed., Wiley 1998, eq. (14.38)–(14.39).

import Definitions.Def_Larmor_em_fields
import Definitions.Def_Larmor_lienard_wiechert

namespace Larmor

theorem angular_distribution (q ε₀ c R : ℝ) (hε : 0 < ε₀) (hc : 0 < c) (hR : 0 < R)
    (w : ℝ → Vec) (hw0 : w 0 = 0) (hv0 : deriv w 0 = 0) (x : Vec) (hx : ‖x‖ = R) :
    inner ℝ (poynting ε₀ c (lwE q ε₀ c w 0 x) (lwB q ε₀ c w 0 x)) (R⁻¹ • x)
      = q ^ 2 * (‖deriv (deriv w) 0‖ ^ 2 - (inner ℝ (deriv (deriv w) 0) (R⁻¹ • x) : ℝ) ^ 2)
        / (16 * Real.pi ^ 2 * ε₀ * c ^ 3 * R ^ 2) := by sorry

end Larmor
