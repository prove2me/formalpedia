-- Prove2me | Theorems.Thm_OAI_MaximalSeshadri_Geometry_Surface_eventual_etale_affine_section_test
-- name    : OAI.MaximalSeshadri.Geometry.Surface.eventual_etale_affine_section_test
-- status  : Open
-- author  : @wurtle
-- created : 2026-11-04T15:06:39.070764+00:00
-- url     : https://prove2.me/theorems/f9e0a526-c4bd-478a-a9af-acbb369726dc
-- title:
--   An eventual homogeneous section test on an étale chart
-- statement:
--   For $L$ ample on a surface $S$ there are an affine open $U$, a trivialization of $L$ on $U$, functions $t_1,t_2$ giving an étale map to the plane, and $r_0>0$ such that: for $r\ge r_0$ and $k,m>0$ with $k\sqrt{L^2/r}<m$, there are $r$ distinct $\mathbb C$-points $p_i$ of $\Gamma(U)$ such that every section $s$ of $L^k$ with coefficient in $(\ker p_i)^m$ for all $i$ is zero.
--
--   **Notation.** $L^2$ is `selfIntersection`, namely $\chi(L^2)-2\chi(L)+\chi(\mathcal O_S)$. `IsAmple` means that for each point $x$ and open $V\ni x$, some positive power has a global section with nonvanishing open containing $x$, inside $V$, and affine. A `Surface` is an integral scheme smooth of relative dimension 2 over $\operatorname{Spec}\mathbb C$ with a closed immersion into some complex projective space over $\mathbb C$.
--
--   **Formalization Note** The statement is verbatim from OpenAI's Lean development, with `Definitions` files of this development imported in place of the upstream modules; these are supporting code for the statement.
-- source:
--   OpenAI, Maximal Seshadri constants on arbitrary polarized surfaces, September 23, 2026, https://github.com/openai/math (paper: preprints/Maximal-Seshadri-Constants-on-Arbitrary-Polarized-Surfaces-September-23-2026/main.pdf; Lean: lean/OAI/AlgebraicGeometry/Seshadri, Apache License 2.0); Lean declaration `OAI.MaximalSeshadri.Geometry.Surface.eventual_etale_affine_section_test`, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/AlgebraicGeometry/Seshadri/Geometry/EtaleAffineTest.lean#L22

import Mathlib
import Definitions.Def_MaximalSeshadriConstants
import Definitions.Def_SeshadriPrelim6

namespace OAI

section

namespace MaximalSeshadri.Geometry
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open MaximalSeshadri.Frames MaximalSeshadri.ProjectiveBertini
open MaximalSeshadri.AnalyticCoordinates MaximalSeshadri.AlgebraicJets
open MaximalSeshadri.ActualInterpolation MaximalSeshadri.LocalComparison

theorem Surface.eventual_etale_affine_section_test (S : Surface)
    (L : LineBundle S.scheme) (hL : L.IsAmple) :
    ∃ U : S.scheme.affineOpens, ∃ eL : L.sheaf.restrict U.1.ι ≅ O U.1.toScheme,
      ∃ t : Fin 2 → Γ(S.scheme,U.1),
      (MvPolynomial.eval₂Hom (openScalars S.structureMap U.1) t).Etale ∧
      letI : Algebra ℂ Γ(S.scheme,U.1) := (openScalars S.structureMap U.1).toAlgebra
      ∃ r₀ : ℕ, 0 < r₀ ∧ ∀ r : ℕ, r₀ ≤ r → ∀ k m : ℕ,
        0 < k → 0 < m → (k:ℝ)*Real.sqrt ((selfIntersection S L:ℝ)/r) < (m:ℝ) →
        ∃ p : Fin r → (Γ(S.scheme,U.1) →ₐ[ℂ] ℂ), Function.Injective p ∧
          ∀ s : O S.scheme ⟶ (L.pow k).sheaf,
            (∀ i, affineCoefficient U (localPowerFrame U.1 eL k) s ∈
              (RingHom.ker (p i))^m) → s = 0 := by
  sorry

end
end MaximalSeshadri.Geometry
end
end OAI
