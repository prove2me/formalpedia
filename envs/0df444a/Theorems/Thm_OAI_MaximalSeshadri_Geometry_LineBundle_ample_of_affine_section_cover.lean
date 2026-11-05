-- Prove2me | Theorems.Thm_OAI_MaximalSeshadri_Geometry_LineBundle_ample_of_affine_section_cover
-- name    : OAI.MaximalSeshadri.Geometry.LineBundle.ample_of_affine_section_cover
-- status  : Open
-- author  : @wurtle
-- created : 2026-11-04T15:06:42.510407+00:00
-- url     : https://prove2.me/theorems/6308c7f2-5348-4242-9b80-058df9dea587
-- title:
--   Ampleness from an affine section cover
-- statement:
--   Let $X$ be integral and compact, $L$ a line bundle, and $s$ a family of global sections whose nonvanishing opens cover $X$ and are affine. Then $L$ is ample.
--
--   **Notation.** `sectionOpen X s` is the same union for a global section $s$: its nonvanishing open. `IsAmple` means that for each point $x$ and open $V\ni x$, some positive power has a global section with nonvanishing open containing $x$, inside $V$, and affine.
--
--   **Formalization Note** The statement is verbatim from OpenAI's Lean development, with `Definitions` files of this development imported in place of the upstream modules; these are supporting code for the statement.
-- source:
--   OpenAI, Maximal Seshadri constants on arbitrary polarized surfaces, September 23, 2026, https://github.com/openai/math (paper: preprints/Maximal-Seshadri-Constants-on-Arbitrary-Polarized-Surfaces-September-23-2026/main.pdf; Lean: lean/OAI/AlgebraicGeometry/Seshadri, Apache License 2.0); Lean declaration `OAI.MaximalSeshadri.Geometry.LineBundle.ample_of_affine_section_cover`, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/AlgebraicGeometry/Seshadri/Geometry/AmpleFromCover.lean#L56

import Mathlib
import Definitions.Def_MaximalSeshadriConstants
import Definitions.Def_SeshadriPrelim6

namespace OAI

section

namespace MaximalSeshadri.Geometry
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open MaximalSeshadri.Frames MaximalSeshadri.Projective MaximalSeshadri.TensorPure

variable {X : Scheme.{0}}

theorem LineBundle.ample_of_affine_section_cover [IsIntegral X] [CompactSpace X]
    (L : LineBundle X) {ι : Type*} (s : ι → (O X ⟶ L.sheaf))
    (hc : (⨆ i, sectionOpen X (s i)) = ⊤)
    (ha : ∀ i, IsAffineOpen (sectionOpen X (s i))) : L.IsAmple := by
  sorry

end
end MaximalSeshadri.Geometry
end
end OAI
