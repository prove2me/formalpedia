-- Prove2me | Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_nonempty_iso_tensorUnit_of_hom_eigenSubdatum_one_of_bijective_smul_eigenOne
-- name    : GoodReductionJacobian.RelativeGroupLaw.nonempty_iso_tensorUnit_of_hom_eigenSubdatum_one_of_bijective_smul_eigenOne
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:53.637625+00:00
-- url     : https://prove2.me/theorems/f0bd506b-9bc7-5b96-b05d-f544f5c639fc
-- title:
--   Invariant part of [n]_*𝒪_A is trivial
-- statement:
--   Let $R$ be a commutative ring, $A$ a scheme and $f : A \to \operatorname{Spec} R$ a morphism, and let $L$ be a relative group law on $f$, i.e. a functorial group structure on the sets $\{\varphi : T \to A \mid \varphi \circ f = t\}$ of $T$-points over $\operatorname{Spec} R$, natural in $T$. Fix $n \in \mathbb{N}$ and assume that every $n$-torsion point $x$ of the group of sections over $\operatorname{Spec} R$ itself (i.e. $x$ in `L.torsionSubset` for the identity base change) satisfies $L.translate\ x$ followed by the multiplication-by-$n$ morphism $[n] =$ `L.schemeNsmul n` $: A \to A$ equal to $[n]$; call this hypothesis $hG$. Let $N$ be a sheaf of $\mathcal{O}_A$-modules. The $\mathcal{O}$-module presheaf `L.eigenSubdatum n hG 1` assigns to an open $U \subseteq A$ the eigensubmodule for the trivial character inside $\Gamma(A, [n]^{-1}U)$, with the evident restrictions and $\Gamma(A,U)$-action; `OModulePresheaf.ofModules f N` assigns to $U$ the sections $\Gamma(N,U)$. Assume given two morphisms of such presheaves, $\varphi$ from $N$'s sections datum to the eigen-datum and $\psi$ in the other direction — each a family of $R$-linear maps on opens commuting with multiplication by sections of $\mathcal{O}_A$ and with restriction — which are mutually inverse open by open (hypotheses $h$ and $h'$). Assume further that for every affine open $U$ of $A$ the map $a \mapsto a \cdot \mathbf{1}$ from $\Gamma(A,U)$ to the eigen-module over $U$ is bijective, where $\mathbf{1} =$ `L.eigenOne n hG U` is the unit section $1 \in \Gamma(A, [n]^{-1}U)$. Then the type of isomorphisms $N \cong \mathbf{1}_{A.\mathrm{Modules}}$ is nonempty, i.e. $N$ is isomorphic to the monoidal unit of the category of $\mathcal{O}_A$-modules.
--
--   This is the trivialisation step in the eigen-decomposition of $[n]_*\mathcal{O}_A$ along multiplication by $n$ on a scheme with a relative group law: the eigencomponent for the trivial character, when it is freely generated over $\mathcal{O}_A$ by the unit section on affine opens, is the structure sheaf. It is used in the construction of the filtration of `pushforwardUnit f (L.schemeNsmul n)` by affine short exact sequences in the good-reduction study of Jacobians.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GoodReductionJacobian_RelativeGroupLaw_nonempty_iso_tensorUnit_of_hom_eigenSubdatum_one_of_bijective_smul_eigenOne.lean

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

theorem GoodReductionJacobian.RelativeGroupLaw.nonempty_iso_tensorUnit_of_hom_eigenSubdatum_one_of_bijective_smul_eigenOne
    {R : Type u} [CommRing R] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)}
    (L : RelativeGroupLaw R f) (n : ℕ)
    (hG : ∀ x ∈ L.torsionSubset (𝟙 (Spec (CommRingCat.of R))) n, L.translate x ≫ L.schemeNsmul n = L.schemeNsmul n)
    (N : A.Modules)
    (φ : OModulePresheaf.Hom (OModulePresheaf.ofModules f N) (L.eigenSubdatum n hG 1))
    (ψ : OModulePresheaf.Hom (L.eigenSubdatum n hG 1) (OModulePresheaf.ofModules f N))
    (h : ∀ (U : A.Opens) (s : (L.eigenSubdatum n hG 1).obj U), φ.app U (ψ.app U s) = s)
    (h' : ∀ (U : A.Opens) (s : (OModulePresheaf.ofModules f N).obj U), ψ.app U (φ.app U s) = s)
    (hone : ∀ U : A.affineOpens, Function.Bijective (fun a : Γ(A, U.1) => a • L.eigenOne n hG U.1)) :
    Nonempty (N ≅ 𝟙_ (A.Modules)) := by sorry
