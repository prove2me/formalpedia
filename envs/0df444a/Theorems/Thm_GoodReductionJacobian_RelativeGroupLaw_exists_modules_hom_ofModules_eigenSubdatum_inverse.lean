-- Prove2me | Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_exists_modules_hom_ofModules_eigenSubdatum_inverse
-- name    : GoodReductionJacobian.RelativeGroupLaw.exists_modules_hom_ofModules_eigenSubdatum_inverse
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:53.637625+00:00
-- url     : https://prove2.me/theorems/ab78e53c-bdd0-5595-be4c-b5f87dd7edfc
-- title:
--   χ-eigen-subdatum of [n]_*mathcal O_A comes from a module sheaf
-- statement:
--   Let $R$ be a commutative ring, $A$ a scheme and $f : A \to \operatorname{Spec} R$ a morphism, and let $L$ be a `RelativeGroupLaw` for $f$: a functorial group structure on the sets $\mathrm{SchemeHomOver}\,t\,f$ of morphisms $T \to A$ over a given $t : T \to \operatorname{Spec} R$, with multiplication, unit and inverse satisfying associativity, the two unit laws and left inverses, and with multiplication compatible with precomposition by any $\psi : T' \to T$ over $\operatorname{Spec} R$. Fix $n \in \mathbb N$, write $[n] =$ `L.schemeNsmul n` for the induced endomorphism of $A$ and, for an $R$-point $x$, write $T_x =$ `L.translate x` for the endomorphism of $A$ given by multiplication by $f$ followed by $x$. Assume $[n] \circ T_x = [n]$ for every $x$ in `L.torsionSubset (𝟙 (Spec (CommRingCat.of R))) n`, the set of $R$-points satisfying `L.IsTorsionPoint` for $n$, and let $\chi$ be an arbitrary function from $R$-points of $f$ to $R$. The conclusion is that there exist a sheaf of modules $N$ over the structure sheaf of $A$ and morphisms $\varphi$ from `OModulePresheaf.ofModules f N` (the datum $U \mapsto \Gamma(N,U)$, with its $R$- and $\Gamma(A,U)$-actions and restriction maps) to `L.eigenSubdatum n hG χ` (the datum $U \mapsto$ `L.eigenSubmodule n hG χ U`, a submodule of $\Gamma(A,[n]^{-1}U)$, with the restrictions and $\Gamma(A,U)$-action inherited from the pushforward `OModulePresheaf.pushforwardUnit f (L.schemeNsmul n)`), and $\psi$ in the opposite direction — each consisting of $R$-linear maps on sections over every open, compatible with the $\Gamma(A,U)$-action and with restriction — such that on every open $U$ the two composites are the identity on sections.
--
--   This identifies the $\chi$-eigen-part of $[n]_*\mathcal O_A$, cut out by the eigen-equations for the translations by $n$-torsion $R$-points, as the sections datum of an honest sheaf of $\mathcal O_A$-modules, i.e. it verifies that the eigen-subdatum satisfies the sheaf condition and can be packaged as an object of `A.Modules`. It is used in the construction of the filtration of `pushforwardUnit f (L.schemeNsmul n)` by eigen-pieces for the abelian-scheme property bundle.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GoodReductionJacobian_RelativeGroupLaw_exists_modules_hom_ofModules_eigenSubdatum_inverse.lean

import Mathlib
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawKernel
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawTranslate
import Definitions.Def_GoodReductionJacobian_NsmulEigenSubdatum
import Definitions.Def_AlgebraicGeometry_OModulePresheafConstructions
import Definitions.Def_AlgebraicGeometry_OModulePresheafOfModules
import Definitions.Def_SheafOfModules_MonoidalV2
import Definitions.Def_AlgebraicGeometry_ModulesTensorPowV2
import Definitions.Def_AlgebraicGeometry_ModulesSectionsTensorV2
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian

universe u

theorem GoodReductionJacobian.RelativeGroupLaw.exists_modules_hom_ofModules_eigenSubdatum_inverse
    {R : Type u} [CommRing R] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)}
    (L : RelativeGroupLaw R f) (n : ℕ)
    (hG : ∀ x ∈ L.torsionSubset (𝟙 (Spec (CommRingCat.of R))) n, L.translate x ≫ L.schemeNsmul n = L.schemeNsmul n)
    (χ : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) f → R) :
    ∃ (N : A.Modules) (φ : OModulePresheaf.Hom (OModulePresheaf.ofModules f N) (L.eigenSubdatum n hG χ))
      (ψ : OModulePresheaf.Hom (L.eigenSubdatum n hG χ) (OModulePresheaf.ofModules f N)),
      (∀ (U : A.Opens) (s : (L.eigenSubdatum n hG χ).obj U), φ.app U (ψ.app U s) = s) ∧
      (∀ (U : A.Opens) (s : (OModulePresheaf.ofModules f N).obj U), ψ.app U (φ.app U s) = s) := by sorry
