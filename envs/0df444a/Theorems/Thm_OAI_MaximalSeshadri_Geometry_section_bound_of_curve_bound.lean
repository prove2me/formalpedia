-- Prove2me | Theorems.Thm_OAI_MaximalSeshadri_Geometry_section_bound_of_curve_bound
-- name    : OAI.MaximalSeshadri.Geometry.section_bound_of_curve_bound
-- status  : Open
-- author  : @wurtle
-- created : 2026-11-04T15:06:07.018977+00:00
-- url     : https://prove2.me/theorems/fdcaecc4-be65-4aa1-8a7c-5d5f60529708
-- title:
--   Vanishing orders of sections are bounded by curve bounds
-- statement:
--   Let $L$ be ample on a surface $S$, $p$ a configuration of $r$ points, and $a\ge0$ with $a\operatorname{mult}_p(C)\le\deg_CL$ for all integral curves $C$. If $M$ is a line bundle, $s\ne0$ a section, and at each $p_i$ the coefficient of $s$ in a frame lies in $(\ker\rho_i)^{n_i}$, then $a\sum_in_i\le L\cdot M$, where $L\cdot M$ is `mixedEuler S L M`.
--
--   **Notation.** $L\cdot M$ is `mixedEuler`, namely $\chi(L\otimes M)-\chi(L)-\chi(M)+\chi(\mathcal O_S)$. $\deg_CL$ is `curveDegree`, namely $\chi(L|_C)-\chi(\mathcal O_C)$. $\operatorname{mult}_p(C)$ is `totalMultiplicity`, the sum over the points of `curveMultiplicity`, the order of the kernel ideal of the local ring map of $C$ at the point. `IsAmple` means that for each point $x$ and open $V\ni x$, some positive power has a global section with nonvanishing open containing $x$, inside $V$, and affine. A `Surface` is an integral scheme smooth of relative dimension 2 over $\operatorname{Spec}\mathbb C$ with a closed immersion into some complex projective space over $\mathbb C$. An `IntegralCurve` on a surface is an integral closed subscheme of topological Krull dimension one, given by a closed immersion. `Configuration S r` is the set of $r$-tuples of complex points with distinct images, with the Zariski topology induced from the product.
--
--   **Formalization Note** The statement is verbatim from OpenAI's Lean development, with `Definitions` files of this development imported in place of the upstream modules; these are supporting code for the statement.
-- source:
--   OpenAI, Maximal Seshadri constants on arbitrary polarized surfaces, September 23, 2026, https://github.com/openai/math (paper: preprints/Maximal-Seshadri-Constants-on-Arbitrary-Polarized-Surfaces-September-23-2026/main.pdf; Lean: lean/OAI/AlgebraicGeometry/Seshadri, Apache License 2.0); Lean declaration `OAI.MaximalSeshadri.Geometry.section_bound_of_curve_bound`, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/AlgebraicGeometry/Seshadri/Divisors/SectionCurveBound.lean#L105

import Mathlib
import Definitions.Def_MaximalSeshadriConstants
import Definitions.Def_SeshadriPrelim6

namespace OAI

section

namespace MaximalSeshadri.Geometry
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open MaximalSeshadri.Frames MaximalSeshadri.ProjectiveBertini

theorem section_bound_of_curve_bound (S : Surface) (L : LineBundle S.scheme)
    (hL : L.IsAmple) {r : ℕ} (p : Configuration S r) (a : ℝ) (ha : 0 ≤ a)
    (hC : ∀ C : IntegralCurve S,
      a*(totalMultiplicity S r C p:ℝ) ≤ (curveDegree S L C:ℝ))
    (M : LineBundle S.scheme) (s : O S.scheme ⟶ M.sheaf) (hs : s ≠ 0)
    (U : Fin r → S.scheme.affineOpens)
    (e : ∀ i, M.sheaf.restrict (U i).1.ι ≅ O (U i).1.toScheme)
    (ρ : ∀ i, letI := (openScalars S.structureMap (U i).1).toAlgebra;
      Γ(S.scheme,(U i).1) →ₐ[ℂ] ℂ)
    (hρ : ∀ i, affineComplexPoint S.structureMap (U i) (ρ i) = p.val i)
    (n : Fin r → ℕ)
    (ho : ∀ i, affineCoefficient (U i) (e i) s ∈ (RingHom.ker (ρ i))^(n i)) :
    a*(∑ i, n i:ℕ) ≤ (mixedEuler S L M:ℝ) := by
  sorry

end
end MaximalSeshadri.Geometry
end
end OAI
