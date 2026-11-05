-- Prove2me | Theorems.Thm_OAI_MaximalSeshadri_Geometry_curve_lower_of_homogeneous_section_test
-- name    : OAI.MaximalSeshadri.Geometry.curve_lower_of_homogeneous_section_test
-- status  : Open
-- author  : @wurtle
-- created : 2026-11-04T15:07:11.542905+00:00
-- url     : https://prove2.me/theorems/74c3562f-960a-4bb0-90cd-950c74e87e15
-- title:
--   Curve lower bound from a homogeneous section test
-- statement:
--   Let $L$ be ample on $S$, $r>0$, $p$ a configuration, $U$ affine with a trivialization of $L$, and suppose that for all $k,m>0$ with $k\sqrt{L^2/r}<m$ some $\mathbb C$-points $\rho_i$ of $\Gamma(U)$ over $p_i$ have the property that every section of $L^k$ with coefficient in $(\ker\rho_i)^m$ for all $i$ vanishes. Then $\sqrt{L^2/r}\operatorname{mult}_p(C)\le\deg_CL$ for each integral curve $C$.
--
--   **Notation.** $L^2$ is `selfIntersection`, namely $\chi(L^2)-2\chi(L)+\chi(\mathcal O_S)$. $\deg_CL$ is `curveDegree`, namely $\chi(L|_C)-\chi(\mathcal O_C)$. $\operatorname{mult}_p(C)$ is `totalMultiplicity`, the sum over the points of `curveMultiplicity`, the order of the kernel ideal of the local ring map of $C$ at the point. `IsAmple` means that for each point $x$ and open $V\ni x$, some positive power has a global section with nonvanishing open containing $x$, inside $V$, and affine. A `Surface` is an integral scheme smooth of relative dimension 2 over $\operatorname{Spec}\mathbb C$ with a closed immersion into some complex projective space over $\mathbb C$. An `IntegralCurve` on a surface is an integral closed subscheme of topological Krull dimension one, given by a closed immersion. `Configuration S r` is the set of $r$-tuples of complex points with distinct images, with the Zariski topology induced from the product.
--
--   **Formalization Note** The statement is verbatim from OpenAI's Lean development, with `Definitions` files of this development imported in place of the upstream modules; these are supporting code for the statement.
-- source:
--   OpenAI, Maximal Seshadri constants on arbitrary polarized surfaces, September 23, 2026, https://github.com/openai/math (paper: preprints/Maximal-Seshadri-Constants-on-Arbitrary-Polarized-Surfaces-September-23-2026/main.pdf; Lean: lean/OAI/AlgebraicGeometry/Seshadri, Apache License 2.0); Lean declaration `OAI.MaximalSeshadri.Geometry.curve_lower_of_homogeneous_section_test`, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/AlgebraicGeometry/Seshadri/Interpolation/AllCurveLowerBound.lean#L25

import Mathlib
import Definitions.Def_MaximalSeshadriConstants
import Definitions.Def_SeshadriPrelim6

namespace OAI

section

namespace MaximalSeshadri.Geometry
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open MaximalSeshadri.Frames MaximalSeshadri.ProjectiveBertini

theorem curve_lower_of_homogeneous_section_test (S : Surface)
    (L : LineBundle S.scheme) (hL : L.IsAmple) {r : ℕ} (hr : 0 < r)
    (p : Configuration S r) (U : S.scheme.affineOpens)
    (eL : L.sheaf.restrict U.1.ι ≅ O U.1.toScheme)
    (htest : ∀ k m : ℕ, 0 < k → 0 < m →
      (k:ℝ)*Real.sqrt ((selfIntersection S L:ℝ)/r) < (m:ℝ) →
      ∃ ρ : letI := (openScalars S.structureMap U.1).toAlgebra;
          Fin r → (Γ(S.scheme,U.1) →ₐ[ℂ] ℂ),
        (∀ i, affineComplexPoint S.structureMap U (ρ i) = p.val i) ∧
        ∀ s : O S.scheme ⟶ (L.pow k).sheaf,
          (∀ i, affineCoefficient U (localPowerFrame U.1 eL k) s ∈
            (RingHom.ker (ρ i))^m) → s = 0)
    (C : IntegralCurve S) :
    Real.sqrt ((selfIntersection S L:ℝ)/r) * (totalMultiplicity S r C p:ℝ) ≤
      (curveDegree S L C:ℝ) := by
  sorry

end
end MaximalSeshadri.Geometry
end
end OAI
