-- Prove2me | Theorems.Thm_GaussMagnetism_exists_vector_potential
-- name    : GaussMagnetism.exists_vector_potential
-- status  : Open
-- author  : @Lucas
-- created : 2026-09-27T20:05:07.124247+00:00
-- url     : https://prove2.me/theorems/04d469cd-be88-46a5-b554-f66c49a2c65c
-- title:
--   Divergence-free smooth fields on $\mathbb R^3$ have a vector potential
-- statement:
--   Let $B:\mathbb R^3\to\mathbb R^3$ be a smooth ($C^\infty$) vector field satisfying Gauss's law for magnetism, $\nabla\cdot B=0$ everywhere on $\mathbb R^3$. Then there exists a smooth vector field $A:\mathbb R^3\to\mathbb R^3$, a **magnetic vector potential**, with
--
--   $$\nabla\times A(x)=B(x)\quad\text{for all }x\in\mathbb R^3.$$
--
--   This is the substantial direction of the equivalence between Gauss's law for magnetism and the existence of a vector potential.
--
--   **Formalization Note** Smoothness is `TongEM.SmoothV` (i.e. `ContDiff ℝ ⊤` with `⊤ : ℕ∞`). The whole space $\mathbb R^3$ is the domain; the result is false on general non-simply-shaped domains, which are not considered here.
-- source:
--   Wikipedia, "Gauss's law for magnetism" (uploaded PDF, 5 pp.), p. 2, section 'Vector potential': 'Due to the Helmholtz decomposition theorem, Gauss's law for magnetism is equivalent to the following statement: There exists a vector field A such that B = ∇ × A.'

import Definitions.Def_GaussMagnetism_box_flux

open Larmor TongEM

namespace GaussMagnetism

theorem exists_vector_potential (B : Vec → Vec) (hB : SmoothV B)
    (hdiv : ∀ x, divg B x = 0) :
    ∃ A : Vec → Vec, SmoothV A ∧ ∀ x, curl A x = B x := by sorry

end GaussMagnetism
