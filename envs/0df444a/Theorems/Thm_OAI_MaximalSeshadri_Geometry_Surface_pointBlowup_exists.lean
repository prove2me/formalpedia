-- Prove2me | Theorems.Thm_OAI_MaximalSeshadri_Geometry_Surface_pointBlowup_exists
-- name    : OAI.MaximalSeshadri.Geometry.Surface.pointBlowup_exists
-- status  : Open
-- author  : @wurtle
-- created : 2026-11-04T15:17:36.538766+00:00
-- url     : https://prove2.me/theorems/5f475e9b-db76-4d09-9112-eec625adeb95
-- title:
--   Existence of the point blow-up structure
-- statement:
--   For a surface $S$ with an ample bundle $L$ and any configuration $p$ of $r$ points, a `PointBlowup S r p` exists: a surface with a blow-up of the centre ideal over $\mathbb C$, together with exceptional line bundles presenting the pullbacks of the ideals of each point.
--
--   **Notation.** `IsAmple` means that for each point $x$ and open $V\ni x$, some positive power has a global section with nonvanishing open containing $x$, inside $V$, and affine. A `Surface` is an integral scheme smooth of relative dimension 2 over $\operatorname{Spec}\mathbb C$ with a closed immersion into some complex projective space over $\mathbb C$. `Configuration S r` is the set of $r$-tuples of complex points with distinct images, with the Zariski topology induced from the product.
--
--   **Formalization Note** The statement is verbatim from OpenAI's Lean development, with `Definitions` files of this development imported in place of the upstream modules; these are supporting code for the statement.
-- source:
--   OpenAI, Maximal Seshadri constants on arbitrary polarized surfaces, September 23, 2026, https://github.com/openai/math (paper: preprints/Maximal-Seshadri-Constants-on-Arbitrary-Polarized-Surfaces-September-23-2026/main.pdf; Lean: lean/OAI/AlgebraicGeometry/Seshadri, Apache License 2.0); Lean declaration `OAI.MaximalSeshadri.Geometry.Surface.pointBlowup_exists`, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/AlgebraicGeometry/Seshadri/Blowup/PointBlowupExistence.lean#L73

import Mathlib
import Definitions.Def_MaximalSeshadriConstants
import Definitions.Def_SeshadriPrelim6

namespace OAI

section

namespace MaximalSeshadri.Geometry
noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open MaximalSeshadri.Frames MaximalSeshadri.Projective MaximalSeshadri.SectionOpens

theorem Surface.pointBlowup_exists (S : Surface) (L : LineBundle S.scheme)
    (hL : L.IsAmple) (r : ℕ) (p : Configuration S r) :
    Nonempty (PointBlowup S r p) := by
  sorry

end
end MaximalSeshadri.Geometry
end
end OAI
