-- Prove2me | Theorems.Thm_OAI_MaximalSeshadri_Geometry_surface_configuration_outside_countable_closed
-- name    : OAI.MaximalSeshadri.Geometry.surface_configuration_outside_countable_closed
-- status  : Proved
-- author  : @wurtle
-- created : 2026-11-04T15:07:37.981022+00:00
-- url     : https://prove2.me/theorems/90eb5dde-deb8-42d8-b4d3-57f060234c88
-- title:
--   Configurations avoid countably many proper closed sets
-- statement:
--   For a surface $S$ and $r\in\mathbb N$, given closed proper subsets $Z_k$ ($k\in\mathbb N$) of the space of configurations of $r$ points, there is a configuration outside all $Z_k$.
--
--   **Notation.** A `Surface` is an integral scheme smooth of relative dimension 2 over $\operatorname{Spec}\mathbb C$ with a closed immersion into some complex projective space over $\mathbb C$. `Configuration S r` is the set of $r$-tuples of complex points with distinct images, with the Zariski topology induced from the product.
--
--   **Formalization Note** The statement is verbatim from OpenAI's Lean development, with `Definitions` files of this development imported in place of the upstream modules; these are supporting code for the statement.
-- source:
--   OpenAI, Maximal Seshadri constants on arbitrary polarized surfaces, September 23, 2026, https://github.com/openai/math (paper: preprints/Maximal-Seshadri-Constants-on-Arbitrary-Polarized-Surfaces-September-23-2026/main.pdf; Lean: lean/OAI/AlgebraicGeometry/Seshadri, Apache License 2.0); Lean declaration `OAI.MaximalSeshadri.Geometry.surface_configuration_outside_countable_closed`, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/AlgebraicGeometry/Seshadri/Configurations/Configurations.lean#L530

import Mathlib
import Definitions.Def_MaximalSeshadriConstants
import Definitions.Def_SeshadriPrelim6

namespace OAI

section

namespace MaximalSeshadri
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open scoped AlgebraicGeometry
open scoped TensorProduct

variable {F : Type} [Field F] [IsAlgClosed F] [Uncountable F]

end
end MaximalSeshadri

namespace MaximalSeshadri
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open scoped AlgebraicGeometry

end
end MaximalSeshadri
namespace MaximalSeshadri
noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open scoped AlgebraicGeometry

end
end MaximalSeshadri

namespace MaximalSeshadri
noncomputable section
open CategoryTheory AlgebraicGeometry
open scoped AlgebraicGeometry

end
end MaximalSeshadri

namespace MaximalSeshadri
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open scoped AlgebraicGeometry

variable {F : Type} [Field F]

end
end MaximalSeshadri
namespace MaximalSeshadri.Geometry
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open scoped AlgebraicGeometry

attribute [local instance] MvPolynomial.gradedAlgebra

theorem surface_configuration_outside_countable_closed
    (S : Surface) (r : ℕ) (Z : ℕ → Set (Configuration S r))
    (hclosed : ∀ k, IsClosed (Z k)) (hproper : ∀ k, Z k ≠ Set.univ) :
    ∃ p : Configuration S r, ∀ k, p ∉ Z k := by
  sorry

end
end MaximalSeshadri.Geometry
end
end OAI
