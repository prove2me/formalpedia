-- Prove2me | Theorems.Thm_OAI_MaximalSeshadri_Geometry_nodal_ideal_branch_sum_le_degree
-- name    : OAI.MaximalSeshadri.Geometry.nodal_ideal_branch_sum_le_degree
-- status  : Open
-- author  : @wurtle
-- created : 2026-11-04T15:18:15.08421+00:00
-- url     : https://prove2.me/theorems/8e6595f6-d87a-431e-84ff-5a1c76e4e1ba
-- title:
--   Branch orders on a surface are bounded by the curve degree
-- statement:
--   Let $S$ be a surface with ample $A$, $I$ an ideal sheaf with integral one-dimensional subscheme, $L$ a line bundle, $s$ a section, $U$ an affine open of dimension at most 2 with a trivialization of $L$, $y\in U$ in the support of $I$, $q$ an analytic family of $\mathbb C$-points of $\Gamma(U)$ with exact jets, $g\neq0$ generating $I$ on $U$, $q_z(g)=u(z)z_1z_2$ near 0, $u(0)\ne0$. If the coefficient $f$ of $s$ is not in $(g)$, then the sum of orders of $f$ on the two axes is at most $\deg_{C}L$ where $C$ is the curve of $I$ (`IntegralCurve.ofIdeal`).
--
--   **Notation.** $\deg_CL$ is `curveDegree`, namely $\chi(L|_C)-\chi(\mathcal O_C)$. `IsAmple` means that for each point $x$ and open $V\ni x$, some positive power has a global section with nonvanishing open containing $x$, inside $V$, and affine. A `Surface` is an integral scheme smooth of relative dimension 2 over $\operatorname{Spec}\mathbb C$ with a closed immersion into some complex projective space over $\mathbb C$. An `IntegralCurve` on a surface is an integral closed subscheme of topological Krull dimension one, given by a closed immersion. The Taylor maps (`analyticTaylor`, `bivariateTaylor`) send a function to the power series of $z\mapsto q_z(\cdot)$ at $0$.
--
--   **Formalization Note** The statement is verbatim from OpenAI's Lean development, with `Definitions` files of this development imported in place of the upstream modules; these are supporting code for the statement.
-- source:
--   OpenAI, Maximal Seshadri constants on arbitrary polarized surfaces, September 23, 2026, https://github.com/openai/math (paper: preprints/Maximal-Seshadri-Constants-on-Arbitrary-Polarized-Surfaces-September-23-2026/main.pdf; Lean: lean/OAI/AlgebraicGeometry/Seshadri, Apache License 2.0); Lean declaration `OAI.MaximalSeshadri.Geometry.nodal_ideal_branch_sum_le_degree`, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/AlgebraicGeometry/Seshadri/Nodal/NodalIdealDegree.lean#L26

import Mathlib
import Definitions.Def_MaximalSeshadriConstants
import Definitions.Def_SeshadriPrelim6

namespace OAI

section
noncomputable section

section

namespace MaximalSeshadri.Geometry
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open MaximalSeshadri.ProjectiveBertini MaximalSeshadri.Projective MaximalSeshadri.Frames
open MaximalSeshadri.AnalyticCoordinates MaximalSeshadri.AlgebraicJets
open MaximalSeshadri.LocalComparison MaximalSeshadri.NodalLocal
open scoped Topology

theorem nodal_ideal_branch_sum_le_degree (S : Surface)
    (A : LineBundle S.scheme) (hA : LineBundle.IsAmple S.scheme A)
    (I : S.scheme.IdealSheafData) [IsIntegral I.subscheme]
    (hd : topologicalKrullDim I.subscheme = 1)
    (L : LineBundle S.scheme) (s : O S.scheme ⟶ L.sheaf)
    (U : S.scheme.affineOpens) (y : S.scheme) (hyU : y ∈ U.1) (hyI : y ∈ I.support)
    (e : L.sheaf.restrict U.1.ι ≅ O U.1.toScheme)
    (hR : ringKrullDim Γ(S.scheme,U.1) ≤ 2)
    (q : letI : Algebra ℂ Γ(S.scheme,U.1) := (openScalars S.structureMap U.1).toAlgebra
      (ℂ × ℂ) → (Γ(S.scheme,U.1) →ₐ[ℂ] ℂ))
    (hq : ∀ t, AnalyticAt ℂ (fun z => q z t) 0)
    (hjets : letI : Algebra ℂ Γ(S.scheme,U.1) := (openScalars S.structureMap U.1).toAlgebra
      ∀ n : ℕ,
      RingHom.ker ((Ideal.Quotient.mk (IsLocalRing.maximalIdeal
        (MvPowerSeries (Fin 2) ℂ)^n)).comp (analyticTaylor q hq).toRingHom) =
          (RingHom.ker (q 0))^n ∧
      Function.Surjective ((Ideal.Quotient.mk (IsLocalRing.maximalIdeal
        (MvPowerSeries (Fin 2) ℂ)^n)).comp (analyticTaylor q hq).toRingHom))
    (g : Γ(S.scheme,U.1)) (hg0 : g ≠ 0)
    (hI : I.ideal U = Ideal.span {g})
    (u : (ℂ × ℂ) → ℂ) (hu : AnalyticAt ℂ u 0) (hu0 : u 0 ≠ 0)
    (hg : ∀ᶠ z in 𝓝 0, q z g = u z*z.1*z.2)
    (hf : U.1.topIso.hom (coefficient e (restrictSection U.1.ι s)) ∉ Ideal.span {g}) :
    letI : Algebra ℂ Γ(S.scheme,U.1) := (openScalars S.structureMap U.1).toAlgebra
    let f := U.1.topIso.hom (coefficient e (restrictSection U.1.ι s))
    (((restrictX ℂ (bivariateTaylor q hq f)).order.toNat +
      (restrictZ ℂ (bivariateTaylor q hq f)).order.toNat : ℕ) : ℤ) ≤
      curveDegree S L (IntegralCurve.ofIdeal S I hd) := by
  sorry

end
end MaximalSeshadri.Geometry
end
end
end
end OAI
