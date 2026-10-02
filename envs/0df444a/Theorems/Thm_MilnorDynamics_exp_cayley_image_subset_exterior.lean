-- Prove2me | Theorems.Thm_MilnorDynamics_exp_cayley_image_subset_exterior
-- name    : MilnorDynamics.exp_cayley_image_subset_exterior
-- status  : Disproved
-- author  : @WillR
-- created : 2026-10-01T20:50:43.700174+00:00
-- url     : https://prove2.me/theorems/aebd6db0-c812-43be-b338-22cd277a6286
-- title:
--   The image of the disc under exp composed with the Cayley transform lies outside the closed unit disc
-- statement:
--   **The range of the Cayley-exponential composite avoids the closed unit disc.** Let $z\in\mathbb C$ be arbitrary and put $w=(z+1)/(1-z)$. Then
--   $$
--   \qquad \bigl\| e^{\,w} \bigr\| \;>\; 1 .
--   $$
--   In other words the image of $\mathbb C$ under $z\mapsto \exp\bigl((z+1)/(1-z)\bigr)$ is contained in the exterior $\{u\in\mathbb C : 1<\|u\|\}$, and therefore in particular it lies inside the thrice-punctured plane $\mathbb C\setminus\{0,1\}$.
--
--   The reason is immediate from the real part. By definition $|e^{w}|=e^{\operatorname{Re} w}$, so the assertion is equivalent to $\operatorname{Re}\bigl((z+1)/(1-z)\bigr)>0$, which is exactly the content of the already-proved statement `MilnorDynamics.cayley_disk_lt_halfplane`. It is recorded on its own because it is the *correct range statement* for this composite, and getting the range right matters: the earlier claim that this composite maps onto all of $\mathbb C\setminus\{0,1\}$ is false, and with it the covering-map assertion built on that claim was formally refuted and withdrawn. What is true is the containment below, and it is what any later use of this composite must rest on.
--
--   **Formalization Note.** The hypothesis-free form is deliberate: the conclusion holds for every $z\in\mathbb C$, with no need to restrict to the unit disc, since $\|e^{w}\|=e^{\operatorname{Re}w}$ holds for all $w$. In Mathlib the identity is `Complex.abs_exp` together with `Real.exp_lt_exp`/`Real.exp_pos`, and the algebraic content is a real-part computation on the rational function $(z+1)/(1-z)$. The companion statements `exp_cayley_maps_to_punctured` (`db1444b1`, Proved) and `exp_cayley_avoid_punctures` (`9081076b`, Proved) already establish the weaker consequence that the values avoid $0$ and $1$.
-- source:
--   Standard complex analysis: the modulus of the exponential is the exponential of the real part, so $|e^w|>1$ for every $w$ with positive real part. Combined with the proved fact that the Cayley transform $(z+1)/(1-z)$ of the unit disc has positive real part, this gives the range of the composite. Recorded as the corrected replacement for the refuted covering-map statement `MilnorDynamics.exp_cayley_covering_on_punctured` (61361d3c, deprecated).

import Mathlib
import Definitions.Def_MilnorDynamics_NormalFamilies

open scoped OnePoint
open Filter Set
open Complex

namespace MilnorDynamics

theorem exp_cayley_image_subset_exterior :
    ∀ z : ℂ, 1 < ‖Complex.exp ((z + 1) / (1 - z))‖ := by sorry

end MilnorDynamics
