-- Prove2me | Theorems.Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_finite_isNsmulCharacter_and_ncard_eq_pow_and_bijective_sum_eigenInclusion
-- name    : GoodReductionJacobian.AbelianSchemePropertyBundle.finite_isNsmulCharacter_and_ncard_eq_pow_and_bijective_sum_eigenInclusion
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:49.54035+00:00
-- url     : https://prove2.me/theorems/8cd0214a-fa9e-5482-905b-be18ded8ac16
-- title:
--   Character eigendecomposition of [n]_*𝒪_A on every open
-- statement:
--   Let $K$ be an algebraically closed field, let $f : A \to \operatorname{Spec} K$ be a scheme over $K$, and let $L$ be a `RelativeGroupLaw` for $f$, i.e. a functorial group structure on the sets $\mathrm{SchemeHomOver}\,t\,f$ of $T$-points of $A$ over $K$, assumed commutative; assume moreover `AbelianSchemePropertyBundle K f` ($f$ smooth and proper, with connected fibres and admitting a relative group law) and that $f$ is smooth of relative dimension $g$. Let $n$ be a natural number with $n \neq 0$ in $K$, and assume that for every $n$-torsion point $x$ of $L$ over $\mathrm{id}_{\operatorname{Spec} K}$ the translation `L.translate x` followed by `L.schemeNsmul n` equals `L.schemeNsmul n`. Call a function $\chi$ from the $K$-points $\mathrm{SchemeHomOver}\,\mathrm{id}\,f$ to $K$ an $n$-multiplication character (`L.IsNsmulCharacter n`) when $\chi$ takes the value $1$ off the $n$-torsion subset, $\chi$ of the identity point is $1$, and $\chi(xy) = \chi(x)\chi(y)$ for $n$-torsion $x,y$. The conclusion asserts: the set of such $\chi$ is finite, of cardinality $n^{2g}$; it is closed under pointwise multiplication; each such $\chi$ satisfies $\chi^n = 1$ pointwise; and for every finset $X$ whose members are exactly the $n$-multiplication characters and every open $U \subseteq A$, the map sending a family $(s_\chi)_{\chi \in X}$, with $s_\chi$ a section over $U$ of the eigen-presheaf `L.eigenSubdatum n hG χ`, to $\sum_{\chi \in X} s_\chi$ computed through the inclusions `L.eigenInclusion n hG χ` into the sections over $U$ of `OModulePresheaf.pushforwardUnit f (L.schemeNsmul n)` is bijective.
--
--   This is the eigendecomposition of $[n]_*\mathcal{O}_A$ for an abelian scheme over an algebraically closed field in which $n$ is invertible: the group of $n$-torsion points has order $n^{2g}$ and exponent dividing $n$, its character group has the same order, and the pushforward of the structure sheaf along multiplication by $n$ splits as a direct sum of character eigen-subsheaves, section by section on every open set. It is used in the construction of the filtration of `OModulePresheaf.pushforwardUnit f (L.schemeNsmul n)` by affine short exact sequences.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_finite_isNsmulCharacter_and_ncard_eq_pow_and_bijective_sum_eigenInclusion.lean

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

theorem GoodReductionJacobian.AbelianSchemePropertyBundle.finite_isNsmulCharacter_and_ncard_eq_pow_and_bijective_sum_eigenInclusion
    (K : Type u) [Field K] [IsAlgClosed K] {A : Scheme.{u}} (f : A ⟶ Spec (CommRingCat.of K))
    (L : RelativeGroupLaw K f) (hc : L.IsCommutative) (hA : AbelianSchemePropertyBundle K f)
    (g : ℕ) [SmoothOfRelativeDimension g f]
    (n : ℕ) (hn : (n : K) ≠ 0)
    (hG : ∀ x ∈ L.torsionSubset (𝟙 (Spec (CommRingCat.of K))) n, L.translate x ≫ L.schemeNsmul n = L.schemeNsmul n) :
    {χ : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) f → K | L.IsNsmulCharacter n χ}.Finite ∧
    {χ : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) f → K | L.IsNsmulCharacter n χ}.ncard = n ^ (2 * g) ∧
    (∀ χ ψ : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) f → K,
      L.IsNsmulCharacter n χ → L.IsNsmulCharacter n ψ → L.IsNsmulCharacter n (χ * ψ)) ∧
    (∀ χ : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) f → K, L.IsNsmulCharacter n χ → χ ^ n = 1) ∧
    ∀ (X : Finset (SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) f → K)),
      (∀ χ, χ ∈ X ↔ L.IsNsmulCharacter n χ) →
      ∀ U : A.Opens, Function.Bijective
        (fun s : (χ : ↥X) → (L.eigenSubdatum n hG (χ : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) f → K)).obj U =>
          ∑ χ : ↥X, (L.eigenInclusion n hG (χ : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) f → K)).app U (s χ)) := by sorry
