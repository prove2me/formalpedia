-- Prove2me | Theorems.Thm_GaussMagnetism_gauss_law_magnetism_iff_vector_potential
-- name    : GaussMagnetism.gauss_law_magnetism_iff_vector_potential
-- status  : Open
-- author  : @Lucas
-- created : 2026-09-27T20:12:37.828526+00:00
-- url     : https://prove2.me/theorems/99dcd406-c043-4161-a94f-16579d3388cb
-- title:
--   Gauss's law for magnetism $\iff$ $B=\nabla\times A$ for a vector potential $A$
-- statement:
--   Let $B:\mathbb R^3\to\mathbb R^3$ be a smooth ($C^\infty$) vector field. Then $B$ satisfies Gauss's law for magnetism,
--
--   $$\nabla\cdot B=0\quad\text{on }\mathbb R^3,$$
--
--   if and only if $B$ has a smooth magnetic vector potential: there is a smooth vector field $A:\mathbb R^3\to\mathbb R^3$ with
--
--   $$B=\nabla\times A\quad\text{on }\mathbb R^3.$$
--
--   This is the vector-potential reformulation of the law stated in the source; it underlies the description of magnetism by potentials and the gauge freedom $A\mapsto A+\nabla\varphi$.
--
--   **Formalization Note** Smoothness of $B$ and $A$ is `TongEM.SmoothV`; divergence and curl are `Larmor.divg`, `Larmor.curl` on `Larmor.Vec` $=$ `EuclideanSpace ℝ (Fin 3)`.
-- source:
--   Wikipedia, "Gauss's law for magnetism" (uploaded PDF, 5 pp.), p. 2, section 'Vector potential': 'Gauss's law for magnetism is equivalent to the following statement: There exists a vector field A such that B = ∇ × A.'

import Definitions.Def_GaussMagnetism_box_flux

open Larmor TongEM

namespace GaussMagnetism

theorem gauss_law_magnetism_iff_vector_potential (B : Vec → Vec) (hB : SmoothV B) :
    (∀ x, divg B x = 0) ↔ ∃ A : Vec → Vec, SmoothV A ∧ ∀ x, curl A x = B x := by sorry

end GaussMagnetism
