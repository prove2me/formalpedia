-- Prove2me | Theorems.Thm_OAI_MaximalSeshadri_Geometry_Surface_eventual_very_general_curve_lower
-- name    : OAI.MaximalSeshadri.Geometry.Surface.eventual_very_general_curve_lower
-- status  : Open
-- author  : @wurtle
-- created : 2026-11-04T15:05:35.964909+00:00
-- url     : https://prove2.me/theorems/e60b6195-831b-43c3-9d15-6172256cdbbd
-- title:
--   The curve bound at very general configurations
-- statement:
--   For $L$ ample on $S$ there is $r_0>0$ such that for all $r\ge r_0$ there are proper closed subsets $Z_n$ of the space of configurations of $r$ points, with some configuration avoiding all $Z_n$, such that every configuration avoiding all $Z_n$ satisfies $\sqrt{L^2/r}\operatorname{mult}_p(C)\le\deg_CL$ for all integral curves $C$.
--
--   **Notation.** $L^2$ is `selfIntersection`, namely $\chi(L^2)-2\chi(L)+\chi(\mathcal O_S)$. $\deg_CL$ is `curveDegree`, namely $\chi(L|_C)-\chi(\mathcal O_C)$. $\operatorname{mult}_p(C)$ is `totalMultiplicity`, the sum over the points of `curveMultiplicity`, the order of the kernel ideal of the local ring map of $C$ at the point. `IsAmple` means that for each point $x$ and open $V\ni x$, some positive power has a global section with nonvanishing open containing $x$, inside $V$, and affine. A `Surface` is an integral scheme smooth of relative dimension 2 over $\operatorname{Spec}\mathbb C$ with a closed immersion into some complex projective space over $\mathbb C$. An `IntegralCurve` on a surface is an integral closed subscheme of topological Krull dimension one, given by a closed immersion. `Configuration S r` is the set of $r$-tuples of complex points with distinct images, with the Zariski topology induced from the product.
--
--   **Formalization Note** The statement is verbatim from OpenAI's Lean development, with `Definitions` files of this development imported in place of the upstream modules; these are supporting code for the statement.
-- source:
--   OpenAI, Maximal Seshadri constants on arbitrary polarized surfaces, September 23, 2026, https://github.com/openai/math (paper: preprints/Maximal-Seshadri-Constants-on-Arbitrary-Polarized-Surfaces-September-23-2026/main.pdf; Lean: lean/OAI/AlgebraicGeometry/Seshadri, Apache License 2.0); Lean declaration `OAI.MaximalSeshadri.Geometry.Surface.eventual_very_general_curve_lower`, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/AlgebraicGeometry/Seshadri/Interpolation/AllCurveLowerBound.lean#L122

import Mathlib
import Definitions.Def_MaximalSeshadriConstants
import Definitions.Def_SeshadriPrelim6

namespace OAI

section

namespace MaximalSeshadri.Geometry
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open MaximalSeshadri.Frames MaximalSeshadri.ProjectiveBertini

theorem Surface.eventual_very_general_curve_lower (S : Surface)
    (L : LineBundle S.scheme) (hL : L.IsAmple) :
    ∃ r₀ : ℕ, 0 < r₀ ∧ ∀ r : ℕ, r₀ ≤ r →
      ∃ Z : ℕ → Set (Configuration S r),
        (∀ n, IsClosed (Z n) ∧ Z n ≠ Set.univ) ∧
        (∃ p : Configuration S r, ∀ n, p ∉ Z n) ∧
        ∀ p : Configuration S r, (∀ n, p ∉ Z n) → ∀ C : IntegralCurve S,
          Real.sqrt ((selfIntersection S L:ℝ)/r)*(totalMultiplicity S r C p:ℝ) ≤
            (curveDegree S L C:ℝ) := by
  sorry

end
end MaximalSeshadri.Geometry
end
end OAI
