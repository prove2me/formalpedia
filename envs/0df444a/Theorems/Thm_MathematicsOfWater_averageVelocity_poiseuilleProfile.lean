-- Prove2me | Theorems.Thm_MathematicsOfWater_averageVelocity_poiseuilleProfile
-- name    : MathematicsOfWater.averageVelocity_poiseuilleProfile
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-24T15:58:24.317554+00:00
-- url     : https://prove2.me/theorems/ef9e03c7-5ecb-46d7-bc98-54690c0342bc
-- title:
--   Average velocity of the Poiseuille profile: $\langle v\rangle=\Delta p\,d^2/(32\eta L)$
-- statement:
--   Let $\eta>0$, $L>0$, $d>0$, $\Delta p\in\mathbb R$ and $v_P(r)=\frac{\Delta p}{4\eta L}\big(\frac{d^2}{4}-r^2\big)$. The average velocity over the circular cross-section, defined through $Q=\langle v\rangle\,\pi d^2/4$, is
--
--   $$\langle v\rangle=\frac{\int_0^{d/2}v_P(r)\,2\pi r\,dr}{\pi d^2/4}=\frac{\Delta p\,d^2}{32\,\eta L}.$$
--
--   This is the value used on slide 17 to estimate blood flow speed in capillaries.
--
--   **Formalization Note** Slide 16 prints $\langle v\rangle=\frac{\Delta p\,d^4}{128\eta L}$, which is a typo (it is the flow rate without the factor $\pi$ and has the wrong units); slide 17 uses the correct value $\frac{\Delta p\,d^2}{32\eta L}$, which is what is formalized.
-- source:
--   Lecture 15: The Mathematics of Water, PHYS 461 & 561 (Biophysics), Drexel University, Fall 2011-2012, 11/15/2011, lecturer Luis Cruz (for Brigita Urbanc), www.physics.drexel.edu/~brigita/COURSES/BIOPHYS_2011-2012/, slide 16 (definition of ⟨v⟩ via Q = ⟨v⟩πd²/4) and slide 17 (v = Δp d² / (32 η L))

import Mathlib
import Definitions.Def_MathematicsOfWater_PipeFlow
open Real

namespace MathematicsOfWater
theorem averageVelocity_poiseuilleProfile (η L Δp d : ℝ)
    (hη : 0 < η) (hL : 0 < L) (hd : 0 < d) :
    averageVelocity d (poiseuilleProfile η L Δp d) = Δp * d ^ 2 / (32 * η * L) := by sorry
end MathematicsOfWater
