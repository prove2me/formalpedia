-- Prove2me | Theorems.Thm_GaussMagnetism_divg_eq_zero_iff_boxFlux_eq_zero
-- name    : GaussMagnetism.divg_eq_zero_iff_boxFlux_eq_zero
-- status  : Open
-- author  : @Lucas
-- created : 2026-09-27T20:04:08.440456+00:00
-- url     : https://prove2.me/theorems/7e6e8c54-d2b1-4921-84f7-94fff6b75b69
-- title:
--   Differential and integral forms of Gauss's law for magnetism are equivalent (box surfaces)
-- statement:
--   Let $B:\mathbb R^3\to\mathbb R^3$ be a continuously differentiable vector field. Then the differential form of Gauss's law for magnetism holds,
--
--   $$\nabla\cdot B(x)=0\quad\text{for all }x\in\mathbb R^3,$$
--
--   if and only if the net outward flux of $B$ through the boundary of every axis-parallel box vanishes:
--
--   $$\oint_{\partial\Omega}B\cdot d\mathbf S=0\quad\text{for every box }\Omega=[a_0,b_0]\times[a_1,b_1]\times[a_2,b_2]\text{ with }a_i<b_i.$$
--
--   This is the statement that the differential and integral forms of the law are mathematically equivalent, a consequence of the divergence theorem.
--
--   **Formalization Note** The source quantifies over arbitrary closed surfaces $S$. General closed surfaces and surface integrals over them are not available in Mathlib, so the closed surfaces here are boundaries of non-degenerate axis-parallel boxes (the surface of a cube is one of the source's examples of a closed surface); the flux is the definition `GaussMagnetism.boxFlux`. $B$ is assumed `ContDiff ℝ 1`.
-- source:
--   Wikipedia, "Gauss's law for magnetism" (uploaded PDF, 5 pp.), p. 1, sections 'Differential form' and 'Integral form' ('The integral and differential forms of Gauss's law for magnetism are mathematically equivalent, due to the divergence theorem'); Wikipedia, "Maxwell's equations" (uploaded PDF, 24 pp.), p. 7, section 'Flux and divergence'.

import Definitions.Def_GaussMagnetism_box_flux

open Larmor TongEM

namespace GaussMagnetism

theorem divg_eq_zero_iff_boxFlux_eq_zero (B : Vec → Vec) (hB : ContDiff ℝ 1 B) :
    (∀ x, divg B x = 0) ↔
      ∀ a b : Vec, (∀ i, a i < b i) → boxFlux B a b = 0 := by sorry

end GaussMagnetism
