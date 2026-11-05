-- Prove2me | Theorems.Thm_OAI_MaximalSeshadri_Geometry_Surface_arbitrary_power_euler_quadratic
-- name    : OAI.MaximalSeshadri.Geometry.Surface.arbitrary_power_euler_quadratic
-- status  : Open
-- author  : @wurtle
-- created : 2026-11-04T15:11:41.663772+00:00
-- url     : https://prove2.me/theorems/47b3d1f3-e685-4501-a3ed-e9b2ee5ffa0a
-- title:
--   Quadratic formula for Euler characteristics of powers
-- statement:
--   For $L$ ample on $S$ and any line bundle $M$: $2\chi(M^n)=n(n-1)M^2+2n(\chi(M)-\chi(\mathcal O_S))+2\chi(\mathcal O_S)$.
--
--   **Notation.** $L^2$ is `selfIntersection`, namely $\chi(L^2)-2\chi(L)+\chi(\mathcal O_S)$. $\chi$ is `eulerCharacteristic`: the alternating sum of $\mathbb C$-dimensions of $\operatorname{Ext}^n(\mathcal O,-)$, for $n\le2$ on a surface and $n\le1$ on a curve. `IsAmple` means that for each point $x$ and open $V\ni x$, some positive power has a global section with nonvanishing open containing $x$, inside $V$, and affine. A `Surface` is an integral scheme smooth of relative dimension 2 over $\operatorname{Spec}\mathbb C$ with a closed immersion into some complex projective space over $\mathbb C$.
--
--   **Formalization Note** The statement is verbatim from OpenAI's Lean development, with `Definitions` files of this development imported in place of the upstream modules; these are supporting code for the statement.
-- source:
--   OpenAI, Maximal Seshadri constants on arbitrary polarized surfaces, September 23, 2026, https://github.com/openai/math (paper: preprints/Maximal-Seshadri-Constants-on-Arbitrary-Polarized-Surfaces-September-23-2026/main.pdf; Lean: lean/OAI/AlgebraicGeometry/Seshadri, Apache License 2.0); Lean declaration `OAI.MaximalSeshadri.Geometry.Surface.arbitrary_power_euler_quadratic`, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/AlgebraicGeometry/Seshadri/Intersection/GeneralSurfaceEuler.lean#L20

import Mathlib
import Definitions.Def_MaximalSeshadriConstants
import Definitions.Def_SeshadriPrelim6

namespace OAI

section

namespace MaximalSeshadri.Geometry
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open MaximalSeshadri.Frames MaximalSeshadri.Projective

theorem Surface.arbitrary_power_euler_quadratic (S : Surface)
    (L : LineBundle S.scheme) (hL : L.IsAmple) (M : LineBundle S.scheme) (n : ℕ) :
    2*eulerCharacteristic S.structureMap 2 (M.pow n).sheaf =
      (n : ℤ)*((n : ℤ)-1)*selfIntersection S M +
      2*(n : ℤ)*(eulerCharacteristic S.structureMap 2 M.sheaf -
        eulerCharacteristic S.structureMap 2 (O S.scheme)) +
      2*eulerCharacteristic S.structureMap 2 (O S.scheme) := by
  sorry

end
end MaximalSeshadri.Geometry
end
end OAI
