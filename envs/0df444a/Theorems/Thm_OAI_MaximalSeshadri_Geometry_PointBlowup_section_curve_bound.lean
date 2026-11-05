-- Prove2me | Theorems.Thm_OAI_MaximalSeshadri_Geometry_PointBlowup_section_curve_bound
-- name    : OAI.MaximalSeshadri.Geometry.PointBlowup.section_curve_bound
-- status  : Open
-- author  : @wurtle
-- created : 2026-11-04T15:05:17.466426+00:00
-- url     : https://prove2.me/theorems/08f12306-d98d-4b24-abb7-d313ee21657a
-- title:
--   Sections on the blow-up are bounded by curve bounds
-- statement:
--   Let $S$ be a surface with ample $L$, $p$ a configuration of $r$ points, $B$ a point blow-up of $S$ at $p$ with projection $f$, and $J,\iota$ presenting the pullback of the centre ideal. Let $w\ge0$ with $w\cdot\operatorname{mult}_p(C)\le\deg_C L$ for all integral curves $C$ on $S$. If $k,m\in\mathbb N$ and $q$ is a nonzero section of $J^{m}\otimes f^*L^{k}$ on $B$, then $w\,rm\le k\,L^2$.
--
--   **Notation.** $L^2$ is `selfIntersection`, namely $\chi(L^2)-2\chi(L)+\chi(\mathcal O_S)$. $\deg_CL$ is `curveDegree`, namely $\chi(L|_C)-\chi(\mathcal O_C)$. $\operatorname{mult}_p(C)$ is `totalMultiplicity`, the sum over the points of `curveMultiplicity`, the order of the kernel ideal of the local ring map of $C$ at the point. `PresentsPullbackIdeal I f J ι` says that $\iota:J\to\mathcal O_Y$ is a monomorphism whose image on affine opens is the extension of $I$ along $f$. `IsAmple` means that for each point $x$ and open $V\ni x$, some positive power has a global section with nonvanishing open containing $x$, inside $V$, and affine. A `Surface` is an integral scheme smooth of relative dimension 2 over $\operatorname{Spec}\mathbb C$ with a closed immersion into some complex projective space over $\mathbb C$. An `IntegralCurve` on a surface is an integral closed subscheme of topological Krull dimension one, given by a closed immersion. `Configuration S r` is the set of $r$-tuples of complex points with distinct images, with the Zariski topology induced from the product.
--
--   **Formalization Note** The statement is verbatim from OpenAI's Lean development, with `Definitions` files of this development imported in place of the upstream modules; these are supporting code for the statement.
-- source:
--   OpenAI, Maximal Seshadri constants on arbitrary polarized surfaces, September 23, 2026, https://github.com/openai/math (paper: preprints/Maximal-Seshadri-Constants-on-Arbitrary-Polarized-Surfaces-September-23-2026/main.pdf; Lean: lean/OAI/AlgebraicGeometry/Seshadri, Apache License 2.0); Lean declaration `OAI.MaximalSeshadri.Geometry.PointBlowup.section_curve_bound`, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/AlgebraicGeometry/Seshadri/Blowup/BlowupForbiddenSection.lean#L23

import Mathlib
import Definitions.Def_MaximalSeshadriConstants
import Definitions.Def_SeshadriPrelim6

namespace OAI

section

namespace MaximalSeshadri.Geometry
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open MaximalSeshadri.Frames MaximalSeshadri.ProjectiveBertini

theorem PointBlowup.section_curve_bound (S : Surface) (L : LineBundle S.scheme)
    (hL : L.IsAmple) {r : ℕ} {p : Configuration S r} (B : PointBlowup S r p)
    (J : LineBundle B.surface.scheme) (ι : J.sheaf ⟶ O B.surface.scheme)
    (hJ : PresentsPullbackIdeal (centreIdeal S r p) B.projection J ι)
    (w : ℝ) (hw : 0 ≤ w)
    (hC : ∀ C : IntegralCurve S,
      w*(totalMultiplicity S r C p:ℝ) ≤ (curveDegree S L C:ℝ))
    (k m : ℕ)
    (q : O B.surface.scheme ⟶ ((J.pow m).tensor ((L.pow k).pullback B.projection)).sheaf)
    (hq : q ≠ 0) : w*((r*m:ℕ):ℝ) ≤ (k:ℝ)*selfIntersection S L := by
  sorry

end
end MaximalSeshadri.Geometry
end
end OAI
