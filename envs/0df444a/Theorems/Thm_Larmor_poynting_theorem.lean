-- Prove2me | Theorems.Thm_Larmor_poynting_theorem
-- name    : Larmor.poynting_theorem
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-20T01:08:53.203066+00:00
-- url     : https://prove2.me/theorems/31e87263-2d99-4f47-abac-a729bace7e4c
-- title:
--   Poynting's theorem: $\partial_t u+\nabla\cdot S=-\langle J,E\rangle$
-- statement:
--   **Poynting's theorem.** Let $\varepsilon_0>0$ and $c>0$, and let $\rho$, $J$, $E$, $B$ be a charge density, a current density, an electric field and a magnetic field satisfying Maxwell's equations in SI units. Assume that for each fixed time the fields $E$ and $B$ are differentiable in space, and that for each fixed point they are differentiable in time. Then at every time $t$ and every point $x$,
--
--   $$\frac{\partial u}{\partial t}+\nabla\cdot S=-\langle J,E\rangle,$$
--
--   where
--   $$u=\frac{\varepsilon_0}{2}\bigl(\|E\|^2+c^2\|B\|^2\bigr),\qquad S=\varepsilon_0c^2\,(E\times B)$$
--   are the electromagnetic energy density and the Poynting vector.
--
--   This is the local conservation law for electromagnetic energy: the field energy in a region changes only through the flux of $S$ across its boundary and the work $\langle J,E\rangle$ done on the charges. It is the statement that turns the surface integral of the Poynting vector into "the radiated power", and is therefore the foundation on which the Larmor formula's definition of power rests.
--
--   **Formalization Note** The time derivative is the derivative of $s\mapsto u\bigl(E(s,x),B(s,x)\bigr)$ at $t$, and the divergence is taken in the space variable with the time frozen at $t$.
-- source:
--   J. D. Jackson, Classical Electrodynamics, 3rd ed., Wiley 1998, §6.7, eq. (6.108) (Poynting's theorem); see also https://en.wikipedia.org/wiki/Larmor_formula — Derivation section, where the radiated power is defined as the surface integral of the Poynting vector.

import Definitions.Def_Larmor_em_fields

namespace Larmor

theorem poynting_theorem (ε₀ c : ℝ) (hε : 0 < ε₀) (hc : 0 < c)
    (ρ : ℝ → Vec → ℝ) (J E B : ℝ → Vec → Vec)
    (hmax : IsMaxwell ε₀ c ρ J E B)
    (hEx : ∀ t, Differentiable ℝ (E t)) (hBx : ∀ t, Differentiable ℝ (B t))
    (hEt : ∀ x, Differentiable ℝ fun s => E s x) (hBt : ∀ x, Differentiable ℝ fun s => B s x)
    (t : ℝ) (x : Vec) :
    deriv (fun s => energyDensity ε₀ c (E s x) (B s x)) t
        + divg (fun y => poynting ε₀ c (E t y) (B t y)) x
      = -inner ℝ (J t x) (E t x) := by sorry

end Larmor
