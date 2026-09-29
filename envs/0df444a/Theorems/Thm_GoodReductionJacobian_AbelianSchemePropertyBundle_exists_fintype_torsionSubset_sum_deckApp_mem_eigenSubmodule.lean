-- Prove2me | Theorems.Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_exists_fintype_torsionSubset_sum_deckApp_mem_eigenSubmodule
-- name    : GoodReductionJacobian.AbelianSchemePropertyBundle.exists_fintype_torsionSubset_sum_deckApp_mem_eigenSubmodule
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:49.54035+00:00
-- url     : https://prove2.me/theorems/e50a5e1b-0766-507c-b848-536b191638e0
-- title:
--   Lagrange resolvent over the n-torsion deck group
-- statement:
--   Let $K$ be an algebraically closed field, $A$ a scheme and $f : A \to \operatorname{Spec} K$, and let $L$ be a relative group law for $f$, i.e. a functorial group structure on the sets $\{\varphi : T \to A \mid \varphi \circ f = t\}$ of points of $A$ over $\operatorname{Spec} K$-schemes $t : T \to \operatorname{Spec} K$, compatible with base change. Assume $L$ is commutative, that `AbelianSchemePropertyBundle K f` holds ($f$ smooth and proper, each fibre of $f$ topologically connected, and a relative group law exists), and that $f$ is smooth of relative dimension $g$. Let $n$ be a natural number with $n \neq 0$ in $K$. Write $[n] =$ `L.schemeNsmul n` for the multiplication-by-$n$ endomorphism of $A$ and, for a $K$-point $x$, let `L.translate x` be translation by $x$. Assume every $x$ in the $n$-torsion subset of the $K$-points (those with $n\cdot x$ the identity point) satisfies `L.translate x` followed by $[n]$ equal to $[n]$; this hypothesis $hG$ supplies for each such $x$ the induced ring endomorphism `L.deckApp n x` of $\Gamma(A, [n]^{-1}U)$ for every open $U \subseteq A$, obtained from `appLE` of `L.translate x`. Let $\chi$ be a $K$-valued function on the $K$-points satisfying `IsNsmulCharacter n`: $\chi = 1$ outside the $n$-torsion subset, $\chi$ of the identity point is $1$, and $\chi$ is multiplicative on the $n$-torsion subset. The conclusion asserts that the $n$-torsion subset carries a `Fintype` structure for which, for every open $U \subseteq A$ and every $a \in \Gamma(A, [n]^{-1}U)$, the resolvent $\sum_P \, \chi(P)^{-1}\,\cdot\,(\text{deck operator of }P)(a)$, the sum being over the $n$-torsion points and the scalars $\chi(P)^{-1}$ acting through `L.nsmulConst` (the image of $K$ in $\Gamma(A,[n]^{-1}U)$ under the structure map of $[n]$ followed by $f$), lies in `L.eigenSubmodule n hG χ U`, the submodule of the pushforward presheaf cut out by the predicate `L.IsEigensection n hG χ U`.
--
--   This is the Lagrange-resolvent step in the analysis of the deck action of $A[n]$ on $[n]_*\mathcal{O}_A$: averaging a section against a character produces an eigensection. It feeds [`GoodReductionJacobian.AbelianSchemePropertyBundle.exists_affineOpens_isUnit_eigenSubdatum`](thm.html#GoodReductionJacobian.AbelianSchemePropertyBundle.exists_affineOpens_isUnit_eigenSubdatum), where such resolvents are used to find eigensections that are units on suitable affine opens.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_exists_fintype_torsionSubset_sum_deckApp_mem_eigenSubmodule.lean

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

theorem GoodReductionJacobian.AbelianSchemePropertyBundle.exists_fintype_torsionSubset_sum_deckApp_mem_eigenSubmodule
    (K : Type u) [Field K] [IsAlgClosed K] {A : Scheme.{u}} (f : A ⟶ Spec (CommRingCat.of K))
    (L : RelativeGroupLaw K f) (hc : L.IsCommutative) (hA : AbelianSchemePropertyBundle K f)
    (g : ℕ) [SmoothOfRelativeDimension g f]
    (n : ℕ) (hn : (n : K) ≠ 0)
    (hG : ∀ x ∈ L.torsionSubset (𝟙 (Spec (CommRingCat.of K))) n, L.translate x ≫ L.schemeNsmul n = L.schemeNsmul n)
    (χ : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) f → K) (hχ : L.IsNsmulCharacter n χ) :
    ∃ _ : Fintype ↥(L.torsionSubset (𝟙 (Spec (CommRingCat.of K))) n),
      ∀ (U : A.Opens) (a : Γ(A, (L.schemeNsmul n) ⁻¹ᵁ U)),
        (∑ P : ↥(L.torsionSubset (𝟙 (Spec (CommRingCat.of K))) n),
            L.nsmulConst n U (χ P.1)⁻¹ * (L.deckApp n P.1 (hG P.1 P.2) U).hom a)
          ∈ L.eigenSubmodule n hG χ U := by sorry
