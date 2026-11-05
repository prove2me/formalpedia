-- Prove2me | Theorems.Thm_OAI_MaximalSeshadri_Geometry_LineBundle_affine_openSections_finite
-- name    : OAI.MaximalSeshadri.Geometry.LineBundle.affine_openSections_finite
-- status  : Proved
-- author  : @wurtle
-- created : 2026-11-04T15:18:34.23242+00:00
-- url     : https://prove2.me/theorems/9ede124f-7478-4616-8b3b-4845969d747e
-- title:
--   Sections of a line bundle on an affine scheme are finite
-- statement:
--   For an affine scheme $X$ and a line bundle $L$, `OpenSections L.sheaf ⊤` is a finite $\Gamma(X,\top)$-module.
--
--   **Formalization Note** The statement is verbatim from OpenAI's Lean development, with `Definitions` files of this development imported in place of the upstream modules; these are supporting code for the statement.
-- source:
--   OpenAI, Maximal Seshadri constants on arbitrary polarized surfaces, September 23, 2026, https://github.com/openai/math (paper: preprints/Maximal-Seshadri-Constants-on-Arbitrary-Polarized-Surfaces-September-23-2026/main.pdf; Lean: lean/OAI/AlgebraicGeometry/Seshadri, Apache License 2.0); Lean declaration `OAI.MaximalSeshadri.Geometry.LineBundle.affine_openSections_finite`, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/AlgebraicGeometry/Seshadri/Sheaves/AffineLocalizing.lean#L129

import Mathlib
import Definitions.Def_MaximalSeshadriConstants
import Definitions.Def_SeshadriPrelim6

namespace OAI

section
noncomputable section

section

namespace MaximalSeshadri.Geometry
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite

variable {X Y : Scheme.{0}}

theorem LineBundle.affine_openSections_finite [IsAffine X] (L : LineBundle X) :
    Module.Finite Γ(X,⊤) (OpenSections L.sheaf ⊤) := by
  sorry

end
end MaximalSeshadri.Geometry
end
end
end
end OAI
