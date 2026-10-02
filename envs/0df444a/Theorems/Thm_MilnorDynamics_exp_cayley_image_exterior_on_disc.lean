-- Prove2me | Theorems.Thm_MilnorDynamics_exp_cayley_image_exterior_on_disc
-- name    : MilnorDynamics.exp_cayley_image_exterior_on_disc
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-01T20:54:55.843379+00:00
-- url     : https://prove2.me/theorems/4ed70a1d-f537-4a3c-8dda-0c557f16d87c
-- title:
--   On the unit disc the Cayley-exponential composite has modulus greater than one
-- statement:
--   **Where the Cayley-exponential composite really does leave the closed unit disc.** Let $z$ lie in the open unit disc $\mathbb D=\{z:|z|<1\}$ and put $w=(z+1)/(1-z)$. Then
--   $$
--   \qquad \bigl\| e^{\,w} \bigr\| \;>\; 1 .
--   $$
--   So the image of the disc under $z\mapsto\exp\bigl((z+1)/(1-z)\bigr)$ is contained in the exterior $\{u\in\mathbb C:1<\|u\|\}$, and hence in the thrice-punctured plane $\mathbb C\setminus\{0,1\}$.
--
--   The argument is a two-line consequence of two standard facts. First, the modulus of a complex exponential is the exponential of its real part, $\|e^{w}\|=e^{\operatorname{Re}w}$. Second, the Cayley transform of a point of the disc has strictly positive real part: for $|z|<1$ one has $\operatorname{Re}\bigl((z+1)/(1-z)\bigr)=\frac{1-|z|^2}{|1-z|^2}>0$. Since $e^{\operatorname{Re}w}>e^0=1$, the conclusion follows.
--
--   **The hypothesis on $z$ is essential, and this is the point of the statement.** Without $|z|<1$ the assertion is false: at $z=2$ one has $w=-3$ and $|e^{w}|=e^{-3}<1$, and more generally the Cayley transform is surjective onto $\mathbb C\setminus\{1\}$ and the exponential onto $\mathbb C\setminus\{0\}$, so the composite ranges over all of $\mathbb C\setminus\{0\}$ and in particular attains points of modulus $<1$. An earlier version of this statement without the disc hypothesis has been recorded as `MilnorDynamics.exp_cayley_image_subset_exterior` (`aebd6db0`) and is false; this statement is the corrected form, matching the already-proved `MilnorDynamics.cayley_disk_lt_halfplane` (`a5dd6f7c`).
--
--   **Formalization Note.** The real-part step is exactly the content of the Proved theorem `MilnorDynamics.cayley_disk_lt_halfplane` (`a5dd6f7c`), which states $0<\bigl((z+1)/(1-z)\bigr).\mathrm{re}$ for $z\in\mathbb D$; the remaining step is monotonicity of the real exponential together with the identity $\|\exp w\|=\exp(\operatorname{Re}w)$.
-- source:
--   Standard complex analysis: $|e^w|=e^{\operatorname{Re}w}$ and, for $|z|<1$, $\operatorname{Re}((z+1)/(1-z))=(1-|z|^2)/|1-z|^2>0$. This is the corrected range statement for the Cayley-exponential composite, replacing the refuted and deprecated `MilnorDynamics.exp_cayley_covering_on_punctured` (61361d3c) and the false hypothesis-free `MilnorDynamics.exp_cayley_image_subset_exterior` (aebd6db0).

import Mathlib
import Definitions.Def_MilnorDynamics_NormalFamilies

open scoped OnePoint
open Filter Set
open Complex

namespace MilnorDynamics

theorem exp_cayley_image_exterior_on_disc :
    ∀ z : ℂ, z ∈ Metric.ball 0 1 → 1 < ‖Complex.exp ((z + 1) / (1 - z))‖ := by sorry

end MilnorDynamics
