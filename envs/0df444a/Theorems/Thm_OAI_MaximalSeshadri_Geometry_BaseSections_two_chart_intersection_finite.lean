-- Prove2me | Theorems.Thm_OAI_MaximalSeshadri_Geometry_BaseSections_two_chart_intersection_finite
-- name    : OAI.MaximalSeshadri.Geometry.BaseSections.two_chart_intersection_finite
-- status  : Open
-- author  : @wurtle
-- created : 2026-11-04T15:07:38.10719+00:00
-- url     : https://prove2.me/theorems/318bab2f-f5bd-45fd-a2fa-db056ea5257d
-- title:
--   Two-chart intersection finiteness
-- statement:
--   In the setting of the two-chart cokernel statement, now with both $K[T]\to\Gamma(U)$, $T\mapsto u$, and $K[T]\to\Gamma(V)$, $T\mapsto v$, finite: the intersection of the images of the sections of $L$ and $P$ in the sections of $N$ on $W$ is a finite $K$-module.
--
--   **Formalization Note** The statement is verbatim from OpenAI's Lean development, with `Definitions` files of this development imported in place of the upstream modules; these are supporting code for the statement.
-- source:
--   OpenAI, Maximal Seshadri constants on arbitrary polarized surfaces, September 23, 2026, https://github.com/openai/math (paper: preprints/Maximal-Seshadri-Constants-on-Arbitrary-Polarized-Surfaces-September-23-2026/main.pdf; Lean: lean/OAI/AlgebraicGeometry/Seshadri, Apache License 2.0); Lean declaration `OAI.MaximalSeshadri.Geometry.BaseSections.two_chart_intersection_finite`, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/AlgebraicGeometry/Seshadri/Intersection/TwoChartIntersection.lean#L21

import Mathlib
import Definitions.Def_MaximalSeshadriConstants
import Definitions.Def_SeshadriPrelim6

namespace OAI

section
noncomputable section

section

namespace MaximalSeshadri.Geometry.BaseSections
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open scoped Polynomial

variable {K : Type} [Field K] {U V W : Scheme.{0}} [IsAffine U] [IsAffine V]

theorem two_chart_intersection_finite
    (kU : K →+* Γ(U,⊤)) (kV : K →+* Γ(V,⊤)) (kW : K →+* Γ(W,⊤))
    (a : W ⟶ U) (b : W ⟶ V) [IsOpenImmersion a] [IsOpenImmersion b]
    (hka : a.appTop.hom.comp kU = kW) (hkb : b.appTop.hom.comp kV = kW)
    (u : Γ(U,⊤)) (v : Γ(V,⊤))
    (ha : a.opensRange = U.basicOpen u) (_hb : b.opensRange = V.basicOpen v)
    (huv : a.appTop u * b.appTop v = 1)
    (hu : (Polynomial.eval₂RingHom kU u).Finite)
    (hv : (Polynomial.eval₂RingHom kV v).Finite)
    (L : LineBundle U) (P : LineBundle V) (N : W.Modules)
    (e : L.sheaf.restrict a ≅ N) (d : P.sheaf.restrict b ≅ N) :
    Module.Finite K ↥((chartMap kU kW a hka L.sheaf e).range ⊓
        (chartMap kV kW b hkb P.sheaf d).range) := by
  sorry

end
end MaximalSeshadri.Geometry.BaseSections
end
end
end
end OAI
