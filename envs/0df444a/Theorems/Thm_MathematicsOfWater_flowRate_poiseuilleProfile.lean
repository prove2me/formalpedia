-- Prove2me | Theorems.Thm_MathematicsOfWater_flowRate_poiseuilleProfile
-- name    : MathematicsOfWater.flowRate_poiseuilleProfile
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-24T15:56:48.706055+00:00
-- url     : https://prove2.me/theorems/1d92acee-e47e-46ad-a539-0d5dd260ad1f
-- title:
--   Flow rate of the Poiseuille profile: $Q=\pi\Delta p\,d^4/(128\eta L)$
-- statement:
--   Let $\eta>0$, $L>0$, $d>0$ and $\Delta p\in\mathbb R$, and let $v_P(r)=\frac{\Delta p}{4\eta L}\big(\frac{d^2}{4}-r^2\big)$ be the Poiseuille profile. Then its volumetric flow rate through the cross-section of diameter $d$ is
--
--   $$Q=\int_0^{d/2} v_P(r)\,2\pi r\,dr=\frac{\pi\,\Delta p\,d^4}{128\,\eta L}.$$
--
--   This is the explicit computation behind Poiseuille's law.
-- source:
--   Lecture 15: The Mathematics of Water, PHYS 461 & 561 (Biophysics), Drexel University, Fall 2011-2012, 11/15/2011, lecturer Luis Cruz (for Brigita Urbanc), www.physics.drexel.edu/~brigita/COURSES/BIOPHYS_2011-2012/, slide 16 ("The average velocity and the resulting flow rate are: ... Q = π Δp d^4 / (128 η L)")

import Mathlib
import Definitions.Def_MathematicsOfWater_PipeFlow
open Real

namespace MathematicsOfWater
theorem flowRate_poiseuilleProfile (η L Δp d : ℝ)
    (hη : 0 < η) (hL : 0 < L) (hd : 0 < d) :
    flowRate d (poiseuilleProfile η L Δp d) = π * Δp * d ^ 4 / (128 * η * L) := by sorry
end MathematicsOfWater
