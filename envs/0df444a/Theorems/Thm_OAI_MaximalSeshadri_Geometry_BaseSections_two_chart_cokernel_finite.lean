-- Prove2me | Theorems.Thm_OAI_MaximalSeshadri_Geometry_BaseSections_two_chart_cokernel_finite
-- name    : OAI.MaximalSeshadri.Geometry.BaseSections.two_chart_cokernel_finite
-- status  : Open
-- author  : @wurtle
-- created : 2026-11-04T15:17:58.849739+00:00
-- url     : https://prove2.me/theorems/03f022a4-a572-44a4-9875-13a72b0945d1
-- title:
--   Two-chart cokernel finiteness
-- statement:
--   Let $K$ be a field, $U,V$ affine, $W$ with open immersions to $U$ and $V$ compatible with ring maps from $K$, realized as basic opens of $u\in\Gamma(U)$ and $v\in\Gamma(V)$ with $uv=1$ on $W$, and with $K[T]\to\Gamma(U)$, $T\mapsto u$, finite. For line bundles $L$ on $U$, $P$ on $V$ with a common restriction $N$ to $W$, the sections of $N$ on $W$ modulo the sum of the images of the sections of $L$ and $P$ form a finite $K$-module.
--
--   **Formalization Note** The statement is verbatim from OpenAI's Lean development, with `Definitions` files of this development imported in place of the upstream modules; these are supporting code for the statement.
-- source:
--   OpenAI, Maximal Seshadri constants on arbitrary polarized surfaces, September 23, 2026, https://github.com/openai/math (paper: preprints/Maximal-Seshadri-Constants-on-Arbitrary-Polarized-Surfaces-September-23-2026/main.pdf; Lean: lean/OAI/AlgebraicGeometry/Seshadri, Apache License 2.0); Lean declaration `OAI.MaximalSeshadri.Geometry.BaseSections.two_chart_cokernel_finite`, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/AlgebraicGeometry/Seshadri/Geometry/TwoChartFinite.lean#L21

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

theorem two_chart_cokernel_finite
    (kU : K →+* Γ(U,⊤)) (kV : K →+* Γ(V,⊤)) (kW : K →+* Γ(W,⊤))
    (a : W ⟶ U) (b : W ⟶ V) [IsOpenImmersion a] [IsOpenImmersion b]
    (hka : a.appTop.hom.comp kU = kW) (hkb : b.appTop.hom.comp kV = kW)
    (u : Γ(U,⊤)) (v : Γ(V,⊤))
    (ha : a.opensRange = U.basicOpen u) (hb : b.opensRange = V.basicOpen v)
    (huv : a.appTop u * b.appTop v = 1)
    (hu : (Polynomial.eval₂RingHom kU u).Finite)
    (L : LineBundle U) (P : LineBundle V) (N : W.Modules)
    (e : L.sheaf.restrict a ≅ N) (d : P.sheaf.restrict b ≅ N) :
    Module.Finite K (Sections kW N ⊤ ⧸
      ((chartMap kU kW a hka L.sheaf e).range ⊔
        (chartMap kV kW b hkb P.sheaf d).range)) := by
  sorry

end
end MaximalSeshadri.Geometry.BaseSections
end
end
end
end OAI
