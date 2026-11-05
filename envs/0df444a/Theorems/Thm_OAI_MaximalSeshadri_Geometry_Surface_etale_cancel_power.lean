-- Prove2me | Theorems.Thm_OAI_MaximalSeshadri_Geometry_Surface_etale_cancel_power
-- name    : OAI.MaximalSeshadri.Geometry.Surface.etale_cancel_power
-- status  : Open
-- author  : @wurtle
-- created : 2026-11-04T15:05:33.337429+00:00
-- url     : https://prove2.me/theorems/df04ed9e-9a9b-4c22-92f9-ff7bab48590c
-- title:
--   Cancelling a power in an étale chart
-- statement:
--   Let $U$ be an affine open of a surface with functions $t_1,t_2$ giving an étale map to $\mathbb A^2_{\mathbb C}$, $\rho$ a $\mathbb C$-point of $\Gamma(U)$, and $a,b\in\Gamma(U)$. If $a\notin\mathfrak m^{m+1}$ and $ab\in\mathfrak m^n$, then $b\in\mathfrak m^{n-m}$, where $\mathfrak m=\ker\rho$.
--
--   **Notation.** A `Surface` is an integral scheme smooth of relative dimension 2 over $\operatorname{Spec}\mathbb C$ with a closed immersion into some complex projective space over $\mathbb C$.
--
--   **Formalization Note** The statement is verbatim from OpenAI's Lean development, with `Definitions` files of this development imported in place of the upstream modules; these are supporting code for the statement.
-- source:
--   OpenAI, Maximal Seshadri constants on arbitrary polarized surfaces, September 23, 2026, https://github.com/openai/math (paper: preprints/Maximal-Seshadri-Constants-on-Arbitrary-Polarized-Surfaces-September-23-2026/main.pdf; Lean: lean/OAI/AlgebraicGeometry/Seshadri, Apache License 2.0); Lean declaration `OAI.MaximalSeshadri.Geometry.Surface.etale_cancel_power`, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/AlgebraicGeometry/Seshadri/Divisors/SectionCurveBound.lean#L29

import Mathlib
import Definitions.Def_MaximalSeshadriConstants
import Definitions.Def_SeshadriPrelim6

namespace OAI

section

namespace MaximalSeshadri.Geometry
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open MaximalSeshadri.Frames MaximalSeshadri.ProjectiveBertini

theorem Surface.etale_cancel_power (S : Surface) (U : S.scheme.affineOpens)
    (t : Fin 2 → Γ(S.scheme,U.1))
    (het : (MvPolynomial.eval₂Hom (openScalars S.structureMap U.1) t).Etale)
    (ρ : letI := (openScalars S.structureMap U.1).toAlgebra;
      Γ(S.scheme,U.1) →ₐ[ℂ] ℂ)
    (a b : Γ(S.scheme,U.1)) (n m : ℕ)
    (ha : a ∉ (RingHom.ker ρ)^(m+1)) (hab : a*b ∈ (RingHom.ker ρ)^n) :
    b ∈ (RingHom.ker ρ)^(n-m) := by
  sorry

end
end MaximalSeshadri.Geometry
end
end OAI
