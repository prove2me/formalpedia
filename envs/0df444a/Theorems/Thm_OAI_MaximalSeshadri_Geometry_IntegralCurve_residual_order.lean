-- Prove2me | Theorems.Thm_OAI_MaximalSeshadri_Geometry_IntegralCurve_residual_order
-- name    : OAI.MaximalSeshadri.Geometry.IntegralCurve.residual_order
-- status  : Open
-- author  : @wurtle
-- created : 2026-11-04T15:05:49.666724+00:00
-- url     : https://prove2.me/theorems/bb8b7618-7ea2-4781-a70a-017584d1a864
-- title:
--   Order of vanishing of the residual section
-- statement:
--   Let $C$ be an integral curve on $S$, $J,\iota$ presenting its ideal, $s=q\circ(J\otimes M\to M)$ with $q$ a section of $J\otimes M$, $U$ an affine open with a frame $f$ of $M$, $\rho$ a $\mathbb C$-point of $\Gamma(U)$, and $n$ with coefficient of $s$ in $(\ker\rho)^n$. Then there is an affine open $V$ with a frame of $J\otimes M$ and a $\mathbb C$-point $\sigma$ at the same complex point with the coefficient of $q$ in $(\ker\sigma)^{n-\operatorname{mult}(C,p)}$.
--
--   **Notation.** `PresentsPullbackIdeal I f J ι` says that $\iota:J\to\mathcal O_Y$ is a monomorphism whose image on affine opens is the extension of $I$ along $f$. A `Surface` is an integral scheme smooth of relative dimension 2 over $\operatorname{Spec}\mathbb C$ with a closed immersion into some complex projective space over $\mathbb C$. An `IntegralCurve` on a surface is an integral closed subscheme of topological Krull dimension one, given by a closed immersion.
--
--   **Formalization Note** The statement is verbatim from OpenAI's Lean development, with `Definitions` files of this development imported in place of the upstream modules; these are supporting code for the statement.
-- source:
--   OpenAI, Maximal Seshadri constants on arbitrary polarized surfaces, September 23, 2026, https://github.com/openai/math (paper: preprints/Maximal-Seshadri-Constants-on-Arbitrary-Polarized-Surfaces-September-23-2026/main.pdf; Lean: lean/OAI/AlgebraicGeometry/Seshadri, Apache License 2.0); Lean declaration `OAI.MaximalSeshadri.Geometry.IntegralCurve.residual_order`, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/AlgebraicGeometry/Seshadri/Divisors/SectionCurveBound.lean#L71

import Mathlib
import Definitions.Def_MaximalSeshadriConstants
import Definitions.Def_SeshadriPrelim6

namespace OAI

section

namespace MaximalSeshadri.Geometry
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open MaximalSeshadri.Frames MaximalSeshadri.ProjectiveBertini

theorem IntegralCurve.residual_order (S : Surface) (C : IntegralCurve S)
    (J M : LineBundle S.scheme) (ι : J.sheaf ⟶ O S.scheme)
    (hJ : PresentsPullbackIdeal C.embedding.ker (𝟙 S.scheme) J ι)
    (s : O S.scheme ⟶ M.sheaf) (q : O S.scheme ⟶ (J.tensor M).sheaf)
    (hq : q ≫ tensorInclusion J M ι = s)
    (U : S.scheme.affineOpens) (f : M.sheaf.restrict U.1.ι ≅ O U.1.toScheme)
    (ρ : letI := (openScalars S.structureMap U.1).toAlgebra;
      Γ(S.scheme,U.1) →ₐ[ℂ] ℂ) (n : ℕ)
    (ho : affineCoefficient U f s ∈ (RingHom.ker ρ)^n) :
    ∃ V : S.scheme.affineOpens,
    ∃ e : (J.tensor M).sheaf.restrict V.1.ι ≅ O V.1.toScheme,
    ∃ σ : letI := (openScalars S.structureMap V.1).toAlgebra;
      Γ(S.scheme,V.1) →ₐ[ℂ] ℂ,
      affineComplexPoint S.structureMap V σ = affineComplexPoint S.structureMap U ρ ∧
      affineCoefficient V e q ∈ (RingHom.ker σ)^
        (n-curveMultiplicity S C (affineComplexPoint S.structureMap U ρ)) := by
  sorry

end
end MaximalSeshadri.Geometry
end
end OAI
