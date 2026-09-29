-- Prove2me | Theorems.Thm_MathematicsOfWater_poiseuille_law
-- name    : MathematicsOfWater.poiseuille_law
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-24T16:08:28.702547+00:00
-- url     : https://prove2.me/theorems/84cd5295-ae64-4e1f-8ba0-9a66623d1c08
-- title:
--   Poiseuille's law: $Q=\pi\Delta p\,d^4/(128\eta L)$
-- statement:
--   Consider steady pressure-driven flow of a Newtonian fluid of viscosity $\eta>0$ through a cylindrical pipe of diameter $d>0$ and length $L>0$ with pressure drop $\Delta p=p(0)-p(L)\in\mathbb R$. Let $v(r)$ be the axial velocity at distance $r$ from the axis, and assume
--
--   1. $v$ solves the radial momentum balance $\frac1r\frac{d}{dr}\big(r\frac{dv}{dr}\big)=-\frac{\Delta p}{\eta L}$ for $0<r<d/2$;
--   2. $v$ is finite (bounded) near the axis;
--   3. $v$ satisfies the no-slip condition $v(d/2)=0$ at the wall, continuously from inside.
--
--   Then the volumetric flow rate is
--
--   $$Q=\int_0^{d/2}v(r)\,2\pi r\,dr=\frac{\pi\,\Delta p\,d^4}{128\,\eta L}.$$
--
--   This is Poiseuille's (Hagen–Poiseuille) law: the flow rate scales with the fourth power of the pipe diameter.
--
--   **Formalization Note** The hypotheses are packaged in the definition `IsPipeFlow`; the flow rate is the definition `flowRate`.
-- source:
--   Lecture 15: The Mathematics of Water, PHYS 461 & 561 (Biophysics), Drexel University, Fall 2011-2012, 11/15/2011, lecturer Luis Cruz (for Brigita Urbanc), www.physics.drexel.edu/~brigita/COURSES/BIOPHYS_2011-2012/, slides 13–16 (goal: Q = π Δp d^4 / (128 η L), slide 16)

import Mathlib
import Definitions.Def_MathematicsOfWater_PipeFlow
open Real

namespace MathematicsOfWater
theorem poiseuille_law (η L Δp d : ℝ) (v : ℝ → ℝ)
    (hη : 0 < η) (hL : 0 < L) (hd : 0 < d)
    (hv : IsPipeFlow η L Δp d v) :
    flowRate d v = π * Δp * d ^ 4 / (128 * η * L) := by sorry
end MathematicsOfWater
