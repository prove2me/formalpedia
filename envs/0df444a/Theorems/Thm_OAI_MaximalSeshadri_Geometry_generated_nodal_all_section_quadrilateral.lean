-- Prove2me | Theorems.Thm_OAI_MaximalSeshadri_Geometry_generated_nodal_all_section_quadrilateral
-- name    : OAI.MaximalSeshadri.Geometry.generated_nodal_all_section_quadrilateral
-- status  : Open
-- author  : @wurtle
-- created : 2026-11-04T15:17:59.215316+00:00
-- url     : https://prove2.me/theorems/908b7143-9cd4-43f6-84eb-0b64a1cd3767
-- title:
--   Quadrilateral bound for all sections at a node
-- statement:
--   Let $L$ be ample on $S$, $M\cong L^d$ with $d>0$, and $s$ sections of $M$ with coefficients $v$ whose zero locus is an integral curve through $y\in U$, where $U$ is affine of Krull dimension at most 2 and carries trivializations of $L,M$. Write $g$ for the coefficient of the combination on $U$. Suppose $q$ is an analytic family of $\mathbb C$-points of $\Gamma(U)$ parametrized near $0\in\mathbb C^2$ whose Taylor map has exact jets, and $q_z(g)=u(z)z_1z_2$ near 0 with $u$ analytic, $u(0)\ne0$. If $t\neq0$ is a section of $L^a$ with $a>0$, $w>0$, and $e$ is the lexicographic initial exponent of the Taylor expansion of the coefficient of $t$ for weight $w$, then $e$ lies in `nodeQuadrilateral` with vertices $(0,0)$, $(adL^2w/(1+w),0)$, $(a/d,a/d)$ and $(0,adL^2/(1+w))$.
--
--   **Notation.** $L^2$ is `selfIntersection`, namely $\chi(L^2)-2\chi(L)+\chi(\mathcal O_S)$. The iso-open of $s$ (`SectionOpens.isoOpen s`) is the union of the opens on which the morphism $s$ restricts to an isomorphism. `sectionIdeal k s hs v` is the comap along `sectionsMorphism` of the ideal sheaf of the hyperplane with coefficients $v$; `sectionCombination k s v` is $\sum_j k(v_j)s_j$. `IsAmple` means that for each point $x$ and open $V\ni x$, some positive power has a global section with nonvanishing open containing $x$, inside $V$, and affine. A `Surface` is an integral scheme smooth of relative dimension 2 over $\operatorname{Spec}\mathbb C$ with a closed immersion into some complex projective space over $\mathbb C$. `nodeQuadrilateral a b c` is the convex hull of $(0,0),(a,0),(c,c),(0,b)$. `LexInitial c t e` says that $c_e\ne0$ and $e$ minimizes $p_1+tp_2$ among exponents with nonzero coefficient, ties broken by the smaller second coordinate. The Taylor maps (`analyticTaylor`, `bivariateTaylor`) send a function to the power series of $z\mapsto q_z(\cdot)$ at $0$.
--
--   **Formalization Note** The statement is verbatim from OpenAI's Lean development, with `Definitions` files of this development imported in place of the upstream modules; these are supporting code for the statement.
-- source:
--   OpenAI, Maximal Seshadri constants on arbitrary polarized surfaces, September 23, 2026, https://github.com/openai/math (paper: preprints/Maximal-Seshadri-Constants-on-Arbitrary-Polarized-Surfaces-September-23-2026/main.pdf; Lean: lean/OAI/AlgebraicGeometry/Seshadri, Apache License 2.0); Lean declaration `OAI.MaximalSeshadri.Geometry.generated_nodal_all_section_quadrilateral`, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/AlgebraicGeometry/Seshadri/Interpolation/AllSectionQuadrilateral.lean#L24

import Mathlib
import Definitions.Def_MaximalSeshadriConstants
import Definitions.Def_SeshadriPrelim6

namespace OAI

section

namespace MaximalSeshadri.Geometry
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open MaximalSeshadri.Frames MaximalSeshadri.Projective MaximalSeshadri.NodalLocal
open MaximalSeshadri.ProjectiveBertini
open MaximalSeshadri.AnalyticCoordinates MaximalSeshadri.AlgebraicJets
open MaximalSeshadri.LocalComparison
open scoped Topology

theorem generated_nodal_all_section_quadrilateral (S : Surface)
    (L : LineBundle S.scheme) (hL : L.IsAmple) (M : LineBundle S.scheme)
    (d : ℕ) (hd : 0 < d) (E : M.sheaf ≅ (L.pow d).sheaf)
    {σ : Type} [Fintype σ] (k : ℂ →+* Γ(S.scheme,⊤))
    (s : σ → (O S.scheme ⟶ M.sheaf)) (hs : (⨆ i, SectionOpens.isoOpen (s i)) = ⊤)
    (v : σ → ℂ) (hne : sectionCombination k s v ≠ 0)
    [IsIntegral (sectionIdeal k s hs v).subscheme]
    (hDim : topologicalKrullDim (sectionIdeal k s hs v).subscheme = 1)
    (U : S.scheme.affineOpens) (y : S.scheme) (hyU : y ∈ U.1)
    (hyI : y ∈ (sectionIdeal k s hs v).support)
    (eL : L.sheaf.restrict U.1.ι ≅ O U.1.toScheme)
    (eM : M.sheaf.restrict U.1.ι ≅ O U.1.toScheme)
    (hR : ringKrullDim Γ(S.scheme,U.1) ≤ 2) :
    letI : Algebra ℂ Γ(S.scheme,U.1) := (openScalars S.structureMap U.1).toAlgebra
    let g := affineCoefficient U eM (sectionCombination k s v)
    ∀ (q : (ℂ × ℂ) → (Γ(S.scheme,U.1) →ₐ[ℂ] ℂ))
      (hq : ∀ b, AnalyticAt ℂ (fun z => q z b) 0)
      (_ : ∀ n : ℕ, RingHom.ker ((Ideal.Quotient.mk
        (IsLocalRing.maximalIdeal (MvPowerSeries (Fin 2) ℂ)^n)).comp
        (analyticTaylor q hq).toRingHom) = (RingHom.ker (q 0))^n ∧
        Function.Surjective ((Ideal.Quotient.mk
        (IsLocalRing.maximalIdeal (MvPowerSeries (Fin 2) ℂ)^n)).comp
        (analyticTaylor q hq).toRingHom))
      (u : (ℂ × ℂ) → ℂ) (_ : AnalyticAt ℂ u 0) (_ : u 0 ≠ 0)
      (_ : ∀ᶠ z in 𝓝 0, q z g = u z*z.1*z.2) (_ : q 0 g = 0)
      (a : ℕ) (_ : 0 < a) (t : O S.scheme ⟶ (L.pow a).sheaf) (_ : t ≠ 0)
      (eA : (L.pow a).sheaf.restrict U.1.ι ≅ O U.1.toScheme)
      (w : ℝ) (_ : 0 < w) (p : Exponent),
      LexInitial (bivariateCoeff (bivariateTaylor q hq (affineCoefficient U eA t))) w p →
      ((p.1:ℝ),(p.2:ℝ)) ∈ nodeQuadrilateral
        ((a:ℝ)*((d:ℝ)*(selfIntersection S L:ℝ)*w/(1+w)))
        ((a:ℝ)*((d:ℝ)*(selfIntersection S L:ℝ)/(1+w))) ((a:ℝ)/d) := by
  sorry

end
end MaximalSeshadri.Geometry
end
end OAI
