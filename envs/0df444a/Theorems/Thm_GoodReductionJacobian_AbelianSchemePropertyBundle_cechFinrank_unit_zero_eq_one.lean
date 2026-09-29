-- Prove2me | Theorems.Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_cechFinrank_unit_zero_eq_one
-- name    : GoodReductionJacobian.AbelianSchemePropertyBundle.cechFinrank_unit_zero_eq_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:49.54035+00:00
-- url     : https://prove2.me/theorems/858284d3-35f6-5f50-bc6b-891ebf4f42bb
-- title:
--   Global functions on an abelian variety: check H⁰(mathcal O_A) is one-dimensional
-- statement:
--   Let $K$ be a field and let $f : A \to \operatorname{Spec} K$ be a morphism of schemes from a scheme $A$ to the spectrum of $K$, and suppose `AbelianSchemePropertyBundle K f` holds, i.e. $f$ is smooth, $f$ is proper, the fibre $f^{-1}(s)$ of the underlying map of topological spaces is a connected (in particular nonempty) set for every point $s$ of $\operatorname{Spec} K$, and there exists a relative group law for $f$ over $K$ in the sense of `RelativeGroupLaw`: a functorial multiplication, unit and inversion on the sets of $\operatorname{Spec} K$-morphisms $T \to A$, satisfying associativity, the unit laws and left inverse law, and compatible with precomposition along morphisms $T' \to T$ over $\operatorname{Spec} K$. Let $\mathcal K$ be an ordered affine cover of $A$, that is, a finite linearly ordered index type together with affine opens $U_i$ of $A$ whose supremum is $\top$. The conclusion is that the degree-zero Čech invariant `cechFinrank` of the presheaf `OModulePresheaf.unit f` — the presheaf $U \mapsto \Gamma(A, U)$ with its $K$-algebra structure coming from $f$ and with restriction maps the restriction homomorphisms — on the cover $\mathcal K$ equals $1$: the $K$-dimension of the degree-zero Čech cohomology module $H^0$ of $\mathcal O_A$ computed from $\mathcal K$ is one.
--
--   This is the statement that an abelian variety over a field has only the constant global functions, $\Gamma(A,\mathcal O_A) = K$, recorded in the Čech form used throughout the treatment of line bundles on such schemes. It is cited in the study of polarisations and of elements of the relative $\operatorname{Pic}^0$, and in the identification of global sections over the whole of $A$ with scalars.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_cechFinrank_unit_zero_eq_one.lean

import Mathlib
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_AlgebraicGeometry_OModulePresheafEulerChar

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian

universe u

theorem GoodReductionJacobian.AbelianSchemePropertyBundle.cechFinrank_unit_zero_eq_one
    (K : Type u) [Field K] {A : Scheme.{u}} (f : A ⟶ Spec (CommRingCat.of K))
    (hA : AbelianSchemePropertyBundle K f) (𝒦 : A.OrderedAffineCover) :
    (OModulePresheaf.unit f).cechFinrank 𝒦 0 = 1 := by sorry
