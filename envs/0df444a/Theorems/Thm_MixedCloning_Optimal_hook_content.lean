-- Prove2me | Theorems.Thm_MixedCloning_Optimal_hook_content
-- name    : MixedCloning.Optimal.hook_content
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:05:48.462252+00:00
-- url     : https://prove2.me/theorems/fccdf4a7-354e-4975-b3d7-55d677ec8a34
-- title:
--   Equation (5) — Schur dimension and hook-content formula
-- statement:
--   Let $\lambda$ be a Young diagram of height at most $d$. For a cell $c=(i,j)$ write $c(c)=j-i$ for its content and $h_\lambda(c)$ for its hook length, counting the cell itself, cells to its right and cells below it. The concrete Schur module satisfies
--
--   $$\dim Q^d_\lambda=s_\lambda(1^d)=\prod_{c\in\lambda}\frac{d+c(c)}{h_\lambda(c)}.$$
--
--   Both the module-dimension identity and the product formula are asserted. They connect the tableau-count coefficients to the actual polynomial representations, rather than postulating that connection.
--
--   Differences from the source:
--   - encoding: partitions and tableaux with symbols starting at 1 → YoungDiagram cells and Fin alphabets starting at 0; reason: shifting indices preserves all shapes, orders, counts and contents
--   - encoding: the Schur irrep → image of the tensor Young symmetrizer with its inherited inner product; reason: this concrete model is the same polynomial representation, with cells used as tensor labels
-- source:
--   Dmitry Grinko, Marco Fanizza, Thilo Scharnhorst, Jack Spilecki, Optimal cloning of mixed states, STOC 2027 submission #243 (October 2026), p. 14, Equation (5) and the identification dim(Q) = s(1^d); Stanley [Sta99, Theorem 7.21.2]

import Definitions.Def_MixedCloning_Optimal_Schur

noncomputable section
open Matrix MeasureTheory
open scoped Matrix ComplexConjugate ComplexOrder Matrix.Norms.Elementwise

namespace MixedCloning.Optimal
attribute [local instance] Classical.propDecidable Classical.decEq

theorem hook_content (d : ℕ) (L : YoungDiagram) (hL : height L ≤ d) :
    Module.finrank ℂ (schurModule L d) = schurCount L d ∧
    (schurCount L d : ℝ) = ∏ c ∈ L.cells, ((d : ℝ) + (content c : ℝ)) / hook L c := by sorry

end MixedCloning.Optimal
