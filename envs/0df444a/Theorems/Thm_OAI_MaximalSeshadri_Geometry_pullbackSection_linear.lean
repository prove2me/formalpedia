-- Prove2me | Theorems.Thm_OAI_MaximalSeshadri_Geometry_pullbackSection_linear
-- name    : OAI.MaximalSeshadri.Geometry.pullbackSection_linear
-- status  : Proved
-- author  : @wurtle
-- created : 2026-11-04T15:18:24.298972+00:00
-- url     : https://prove2.me/theorems/54414f38-4570-47d0-be5e-150d2af209cb
-- title:
--   Pullback of sections is $\mathbb C$-linear
-- statement:
--   Let $f:Y\to X$ be a morphism over $\mathbb C$ with $Y$ integral and $L$ a line bundle on $X$. Under `complexSectionModule`, `pullbackSection f` is additive and $\mathbb C$-homogeneous on sections of $L$.
--
--   **Formalization Note** The statement is verbatim from OpenAI's Lean development, with `Definitions` files of this development imported in place of the upstream modules; these are supporting code for the statement.
-- source:
--   OpenAI, Maximal Seshadri constants on arbitrary polarized surfaces, September 23, 2026, https://github.com/openai/math (paper: preprints/Maximal-Seshadri-Constants-on-Arbitrary-Polarized-Surfaces-September-23-2026/main.pdf; Lean: lean/OAI/AlgebraicGeometry/Seshadri, Apache License 2.0); Lean declaration `OAI.MaximalSeshadri.Geometry.pullbackSection_linear`, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/AlgebraicGeometry/Seshadri/Sheaves/PullbackSectionLinear.lean#L20

import Mathlib
import Definitions.Def_MaximalSeshadriConstants
import Definitions.Def_SeshadriPrelim6

namespace OAI

section

namespace MaximalSeshadri.Geometry
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open MaximalSeshadri.Frames MaximalSeshadri.ProjectiveBertini

variable {X Y : Scheme.{0}}

theorem pullbackSection_linear [IsIntegral Y] (g : X ⟶ complexBase) (h : Y ⟶ complexBase)
    (f : Y ⟶ X) (hf : f ≫ g = h) (L : LineBundle X) :
    letI (M : X.Modules) : Module ℂ (O X ⟶ M) := complexSectionModule g M
    letI (M : Y.Modules) : Module ℂ (O Y ⟶ M) := complexSectionModule h M
    (∀ s t : (O X ⟶ L.sheaf), pullbackSection f (s+t) = pullbackSection f s + pullbackSection f t) ∧
    (∀ (c : ℂ) (s : (O X ⟶ L.sheaf)), pullbackSection f (c • s) = c • (pullbackSection f s : (O Y ⟶ (L.pullback f).sheaf))) := by
  sorry

end
end MaximalSeshadri.Geometry
end
end OAI
