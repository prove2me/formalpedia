-- Prove2me | Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_nonempty_tensor_iso_of_hom_eigenSubdatum_of_forall_exists_bijective_smul
-- name    : GoodReductionJacobian.RelativeGroupLaw.nonempty_tensor_iso_of_hom_eigenSubdatum_of_forall_exists_bijective_smul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:55.058405+00:00
-- url     : https://prove2.me/theorems/18875e4c-b688-51cd-af5c-2ed352cad1f2
-- title:
--   Multiplication of eigen-parts of [n]_*mathcal O_A gives a tensor isomorphism
-- statement:
--   Let $R$ be a commutative ring, $A$ a scheme and $f : A \to \operatorname{Spec} R$ a morphism equipped with a relative group law $L$, i.e. a functorial group structure on the sets of $T$-points $\{\varphi : T \to A \mid \varphi \circ f = t\}$, natural in $T$. Let $n$ be a natural number and assume that for every $R$-point $x$ in the $n$-torsion subset of $L$ the translation $L.\mathrm{translate}\,x$ followed by the multiplication-by-$n$ endomorphism $L.\mathrm{schemeNsmul}\,n : A \to A$ equals $L.\mathrm{schemeNsmul}\,n$; call this hypothesis $hG$. Let $\chi, \psi$ be arbitrary functions from the $R$-points of $f$ to $R$ (no multiplicativity is required). For a function $\theta$, `L.eigenSubdatum n hG θ` is the presheaf of $R$-modules on $A$ whose sections over $U$ are the $\theta$-eigensections inside $\Gamma(A, [n]^{-1}U)$, a submodule of the pushforward of $\mathcal O_A$ along $[n]$, with the $\Gamma(A,U)$-action and restriction maps inherited from it. Let $N_1, N_2, N_3$ be $\mathcal O_A$-modules, and suppose given, for each of the three pairs $(N_1, \chi)$, $(N_2, \psi)$, $(N_3, \chi\psi)$ (the last character being the pointwise product), a pair of morphisms of $\mathcal O$-module presheaf data — collections of $R$-linear maps on each open, commuting with multiplication by sections of $\mathcal O_A$ and with restriction — between the sections presheaf of the module and the corresponding eigen-presheaf, which are mutually inverse on sections over every open. Assume finally that every point of $A$ has an affine open neighbourhood $V$ carrying sections $s$ of the $\chi$-eigen-presheaf and $t$ of the $\psi$-eigen-presheaf over $V$ such that, for every affine open $W \subseteq V$, multiplication by elements of $\Gamma(A, W)$ on the restriction of $s$, on the restriction of $t$, and on the restriction of their product $s t$ (an eigensection for $\chi\psi$, formed by multiplying in $\Gamma(A, [n]^{-1}W)$) is bijective, so that each of the three is a frame over $W$. The conclusion is that the type of isomorphisms $N_1 \otimes N_2 \cong N_3$ of $\mathcal O_A$-modules is nonempty.
--
--   This is the multiplicativity of the eigen-decomposition of $[n]_*\mathcal O_A$ under an isogeny whose $n$-torsion translations are deck transformations: the product of sections pairs the $\chi$- and $\psi$-eigen-parts into the $\chi\psi$-eigen-part, and locally free frames make the induced map on the tensor product an isomorphism. It is used in the construction of filtrations of $[n]_*\mathcal O_A$ by eigen-pieces, via [`GoodReductionJacobian.AbelianSchemePropertyBundle.exists_affSES_filtration_pushforwardUnit_schemeNsmul`](thm.html#GoodReductionJacobian.AbelianSchemePropertyBundle.exists_affSES_filtration_pushforwardUnit_schemeNsmul).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GoodReductionJacobian_RelativeGroupLaw_nonempty_tensor_iso_of_hom_eigenSubdatum_of_forall_exists_bijective_smul.lean

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

theorem GoodReductionJacobian.RelativeGroupLaw.nonempty_tensor_iso_of_hom_eigenSubdatum_of_forall_exists_bijective_smul
    {R : Type u} [CommRing R] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)}
    (L : RelativeGroupLaw R f) (n : ℕ)
    (hG : ∀ x ∈ L.torsionSubset (𝟙 (Spec (CommRingCat.of R))) n, L.translate x ≫ L.schemeNsmul n = L.schemeNsmul n)
    (χ ψ : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) f → R)
    (N₁ N₂ N₃ : A.Modules)
    (φ₁ : OModulePresheaf.Hom (OModulePresheaf.ofModules f N₁) (L.eigenSubdatum n hG χ))
    (ψ₁ : OModulePresheaf.Hom (L.eigenSubdatum n hG χ) (OModulePresheaf.ofModules f N₁))
    (h₁ : ∀ (U : A.Opens) (s : (L.eigenSubdatum n hG χ).obj U), φ₁.app U (ψ₁.app U s) = s)
    (h₁' : ∀ (U : A.Opens) (s : (OModulePresheaf.ofModules f N₁).obj U), ψ₁.app U (φ₁.app U s) = s)
    (φ₂ : OModulePresheaf.Hom (OModulePresheaf.ofModules f N₂) (L.eigenSubdatum n hG ψ))
    (ψ₂ : OModulePresheaf.Hom (L.eigenSubdatum n hG ψ) (OModulePresheaf.ofModules f N₂))
    (h₂ : ∀ (U : A.Opens) (s : (L.eigenSubdatum n hG ψ).obj U), φ₂.app U (ψ₂.app U s) = s)
    (h₂' : ∀ (U : A.Opens) (s : (OModulePresheaf.ofModules f N₂).obj U), ψ₂.app U (φ₂.app U s) = s)
    (φ₃ : OModulePresheaf.Hom (OModulePresheaf.ofModules f N₃) (L.eigenSubdatum n hG (χ * ψ)))
    (ψ₃ : OModulePresheaf.Hom (L.eigenSubdatum n hG (χ * ψ)) (OModulePresheaf.ofModules f N₃))
    (h₃ : ∀ (U : A.Opens) (s : (L.eigenSubdatum n hG (χ * ψ)).obj U), φ₃.app U (ψ₃.app U s) = s)
    (h₃' : ∀ (U : A.Opens) (s : (OModulePresheaf.ofModules f N₃).obj U), ψ₃.app U (φ₃.app U s) = s)
    (hfr : ∀ y : A, ∃ V : A.affineOpens, y ∈ V.1 ∧
      ∃ (s : (L.eigenSubdatum n hG χ).obj V.1) (t : (L.eigenSubdatum n hG ψ).obj V.1),
        ∀ (W : A.affineOpens) (hW : W.1 ≤ V.1),
          Function.Bijective (fun a : Γ(A, W.1) => a • (L.eigenSubdatum n hG χ).res hW s) ∧
          Function.Bijective (fun a : Γ(A, W.1) => a • (L.eigenSubdatum n hG ψ).res hW t) ∧
          Function.Bijective (fun a : Γ(A, W.1) => a • (L.eigenSubdatum n hG (χ * ψ)).res hW (L.eigenMul n hG s t))) :
    Nonempty (N₁ ⊗ N₂ ≅ N₃) := by sorry
