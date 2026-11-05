-- Prove2me | Theorems.Thm_OAI_MaximalSeshadri_Geometry_LineBundle_pullbackSection_bijective
-- name    : OAI.MaximalSeshadri.Geometry.LineBundle.pullbackSection_bijective
-- status  : Proved
-- author  : @wurtle
-- created : 2026-11-04T15:18:21.543203+00:00
-- url     : https://prove2.me/theorems/cecb4711-9643-41a5-a120-49da2704141d
-- title:
--   Pullback of sections is bijective when the structure map is an isomorphism
-- statement:
--   Let $f:X\to Y$ be a morphism such that the map $\mathcal O_Y\to f_*\mathcal O_X$ (`IdealModule.structureMap f`) is an isomorphism. For every line bundle $L$ on $Y$ the map $H^0(Y,L)\to H^0(X,f^*L)$ given by `pullbackSection f` is a bijection.
--
--   **Formalization Note** The statement is verbatim from OpenAI's Lean development, with `Definitions` files of this development imported in place of the upstream modules; these are supporting code for the statement.
-- source:
--   OpenAI, Maximal Seshadri constants on arbitrary polarized surfaces, September 23, 2026, https://github.com/openai/math (paper: preprints/Maximal-Seshadri-Constants-on-Arbitrary-Polarized-Surfaces-September-23-2026/main.pdf; Lean: lean/OAI/AlgebraicGeometry/Seshadri, Apache License 2.0); Lean declaration `OAI.MaximalSeshadri.Geometry.LineBundle.pullbackSection_bijective`, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/AlgebraicGeometry/Seshadri/Blowup/BlowupLineDescent.lean#L59

import Mathlib
import Definitions.Def_MaximalSeshadriConstants
import Definitions.Def_SeshadriPrelim6

namespace OAI

section

namespace MaximalSeshadri.Geometry
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open MaximalSeshadri.Frames

variable {X Y : Scheme.{0}} (f : X ⟶ Y)

theorem LineBundle.pullbackSection_bijective [IsIso (IdealModule.structureMap f)]
    (L : LineBundle Y) : Function.Bijective (pullbackSection f (M := L.sheaf)) := by
  sorry

end
end MaximalSeshadri.Geometry
end
end OAI
