-- Prove2me | Theorems.Thm_OAI_MaximalSeshadri_Geometry_Surface_section_contains_curve_of_order
-- name    : OAI.MaximalSeshadri.Geometry.Surface.section_contains_curve_of_order
-- status  : Open
-- author  : @wurtle
-- created : 2026-11-04T15:06:07.484845+00:00
-- url     : https://prove2.me/theorems/d6852874-469d-45f3-afcb-52e7010ad4f7
-- title:
--   A section vanishing to positive order vanishes on a curve
-- statement:
--   Let $M$ be a line bundle on a surface $S$, $s\ne0$ a section, $U$ an affine open with trivialization $e$, $\rho$ a $\mathbb C$-point of $\Gamma(U)$, and $n>0$ with the coefficient of $s$ in $(\ker\rho)^n$. Then there is an integral curve $C$ on $S$ on which $s$ pulls back to zero.
--
--   **Notation.** A `Surface` is an integral scheme smooth of relative dimension 2 over $\operatorname{Spec}\mathbb C$ with a closed immersion into some complex projective space over $\mathbb C$. An `IntegralCurve` on a surface is an integral closed subscheme of topological Krull dimension one, given by a closed immersion.
--
--   **Formalization Note** The statement is verbatim from OpenAI's Lean development, with `Definitions` files of this development imported in place of the upstream modules; these are supporting code for the statement.
-- source:
--   OpenAI, Maximal Seshadri constants on arbitrary polarized surfaces, September 23, 2026, https://github.com/openai/math (paper: preprints/Maximal-Seshadri-Constants-on-Arbitrary-Polarized-Surfaces-September-23-2026/main.pdf; Lean: lean/OAI/AlgebraicGeometry/Seshadri, Apache License 2.0); Lean declaration `OAI.MaximalSeshadri.Geometry.Surface.section_contains_curve_of_order`, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/AlgebraicGeometry/Seshadri/Divisors/SectionCurveBound.lean#L55

import Mathlib
import Definitions.Def_MaximalSeshadriConstants
import Definitions.Def_SeshadriPrelim6

namespace OAI

section

namespace MaximalSeshadri.Geometry
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open MaximalSeshadri.Frames MaximalSeshadri.ProjectiveBertini

theorem Surface.section_contains_curve_of_order (S : Surface) (M : LineBundle S.scheme)
    (s : O S.scheme ⟶ M.sheaf) (hs : s ≠ 0)
    (U : S.scheme.affineOpens) (e : M.sheaf.restrict U.1.ι ≅ O U.1.toScheme)
    (ρ : letI := (openScalars S.structureMap U.1).toAlgebra;
      Γ(S.scheme,U.1) →ₐ[ℂ] ℂ) (n : ℕ) (hn : 0 < n)
    (ho : affineCoefficient U e s ∈ (RingHom.ker ρ)^n) :
    ∃ C : IntegralCurve S, pullbackSection C.embedding s = 0 := by
  sorry

end
end MaximalSeshadri.Geometry
end
end OAI
