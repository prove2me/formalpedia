-- Prove2me | Theorems.Thm_OAI_MaximalSeshadri_Geometry_LineBundle_exists_ample_twist
-- name    : OAI.MaximalSeshadri.Geometry.LineBundle.exists_ample_twist
-- status  : Open
-- author  : @wurtle
-- created : 2026-11-04T15:06:31.648481+00:00
-- url     : https://prove2.me/theorems/5d1782b9-4deb-44c8-8c8d-1e95a2b56ff9
-- title:
--   Twisting by an ample bundle gives ampleness
-- statement:
--   Let $X$ be integral and compact, $L$ ample and $M$ any line bundle. There is $d>0$ with $L^d\otimes M$ ample.
--
--   **Notation.** `IsAmple` means that for each point $x$ and open $V\ni x$, some positive power has a global section with nonvanishing open containing $x$, inside $V$, and affine.
--
--   **Formalization Note** The statement is verbatim from OpenAI's Lean development, with `Definitions` files of this development imported in place of the upstream modules; these are supporting code for the statement.
-- source:
--   OpenAI, Maximal Seshadri constants on arbitrary polarized surfaces, September 23, 2026, https://github.com/openai/math (paper: preprints/Maximal-Seshadri-Constants-on-Arbitrary-Polarized-Surfaces-September-23-2026/main.pdf; Lean: lean/OAI/AlgebraicGeometry/Seshadri, Apache License 2.0); Lean declaration `OAI.MaximalSeshadri.Geometry.LineBundle.exists_ample_twist`, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/AlgebraicGeometry/Seshadri/Geometry/AmpleFromCover.lean#L67

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

theorem LineBundle.exists_ample_twist [IsIntegral X] [CompactSpace X]
    (L M : LineBundle X) (hL : L.IsAmple) :
    ∃ d : ℕ, 0 < d ∧ ((L.pow d).tensor M).IsAmple := by
  sorry

end
end MaximalSeshadri.Geometry
end
end OAI
