-- Prove2me | Theorems.Thm_GaussMagnetism_div_curl_eq_zero
-- name    : GaussMagnetism.div_curl_eq_zero
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-27T19:56:09.669654+00:00
-- url     : https://prove2.me/theorems/f4318d5a-a512-4d5f-86f2-d5226f57822c
-- title:
--   The divergence of a curl vanishes: $\nabla\cdot(\nabla\times A)=0$
-- statement:
--   Let $A:\mathbb R^3\to\mathbb R^3$ be a twice continuously differentiable vector field. Then for every $x\in\mathbb R^3$,
--
--   $$\nabla\cdot(\nabla\times A)(x)=0.$$
--
--   In particular, every magnetic field of the form $B=\nabla\times A$ satisfies Gauss's law for magnetism $\nabla\cdot B=0$; this is the easy direction of the equivalence between Gauss's law for magnetism and the existence of a vector potential.
--
--   **Formalization Note** $C^2$ regularity is stated as `ContDiff ℝ 2 A`.
-- source:
--   Wikipedia, "Gauss's law for magnetism" (uploaded PDF, 5 pp.), p. 2, section 'Vector potential' (Gauss's law for magnetism is equivalent to the existence of A with B = ∇×A); Wikipedia, "Maxwell's equations" (uploaded PDF, 24 pp.), p. 8, 'the div–curl identity' (section 'Charge conservation').

import Definitions.Def_GaussMagnetism_box_flux

open Larmor TongEM

namespace GaussMagnetism

theorem div_curl_eq_zero (A : Vec → Vec) (hA : ContDiff ℝ 2 A) (x : Vec) :
    divg (curl A) x = 0 := by sorry

end GaussMagnetism
