-- Prove2me | Theorems.Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_bijective_smul_eigenOne
-- name    : GoodReductionJacobian.AbelianSchemePropertyBundle.bijective_smul_eigenOne
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:47.88569+00:00
-- url     : https://prove2.me/theorems/d4f1bdfb-2d9a-5676-9917-5acd41901748
-- title:
--   Trivial eigencomponent of [n]_*mathcal O_A is mathcal O_A
-- statement:
--   Let $K$ be an algebraically closed field, let $f : A \to \operatorname{Spec} K$ be a scheme over $K$, and let $L$ be a `RelativeGroupLaw` for $f$, that is, a functorial group structure on the sets $\mathrm{SchemeHomOver}\,t\,f = \{\varphi : T \to A \mid \varphi \circ f = t\}$ of $T$-points over $K$, with multiplication, unit and inverse satisfying associativity, the unit laws and left inverse, and compatible with base change $T' \to T$. Assume $L$ is commutative, that $f$ satisfies `AbelianSchemePropertyBundle` (namely $f$ is smooth and proper, every fibre of $f$ is connected, and $f$ carries a relative group law), and that $f$ is smooth of relative dimension $g$. Let $n$ be a natural number with $n \ne 0$ in $K$, and assume the hypothesis `hG`: for every $K$-point $x$ of $A$ (a section of $f$ over the identity of $\operatorname{Spec} K$) killed by $n$ for $L$, the translation $L.translate\,x$ followed by $[n] = L.schemeNsmul\,n$ — the morphism underlying the $n$-fold sum of the identity point — equals $[n]$. Then for every affine open $U \subseteq A$ the map $a \mapsto a \cdot (L.eigenOne\,n\,hG\,U)$ from $\Gamma(A,U)$ to the value at $U$ of the $\mathcal O$-module presheaf `L.eigenSubdatum n hG 1`, a submodule of $\Gamma(A,[n]^{-1}U)$ on which $\Gamma(A,U)$ acts through $[n]^{\sharp}$, is bijective; here `eigenOne` is the constant section $1 \in \Gamma(A,[n]^{-1}U)$ regarded as an element of that submodule, so the map sends $a$ to $[n]^{\sharp} a$.
--
--   This is the descent of functions along the finite flat surjection $[n]$: on affine opens, pullback along $[n]$ identifies the sections of $\mathcal O_A$ with the part of $[n]_*\mathcal O_A$ belonging to the trivial character, i.e. the sections invariant under translation by the $n$-torsion points. It is used, together with the corresponding statement for the other characters, in [`GoodReductionJacobian.AbelianSchemePropertyBundle.exists_affineOpens_bijective_smul_eigenSubdatum_and_bijective_smul_eigenOne`](thm.html#GoodReductionJacobian.AbelianSchemePropertyBundle.exists_affineOpens_bijective_smul_eigenSubdatum_and_bijective_smul_eigenOne), which provides local frames for the eigencomponents of $[n]_*\mathcal O_A$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_bijective_smul_eigenOne.lean

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

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory NeronModelInfra GoodReductionJacobian
open AlgebraicGeometry

universe u

theorem GoodReductionJacobian.AbelianSchemePropertyBundle.bijective_smul_eigenOne
    (K : Type u) [Field K] [IsAlgClosed K] {A : Scheme.{u}} (f : A ⟶ Spec (CommRingCat.of K))
    (L : RelativeGroupLaw K f) (hc : L.IsCommutative) (hA : AbelianSchemePropertyBundle K f)
    (g : ℕ) [SmoothOfRelativeDimension g f]
    (n : ℕ) (hn : (n : K) ≠ 0)
    (hG : ∀ x ∈ L.torsionSubset (𝟙 (Spec (CommRingCat.of K))) n, L.translate x ≫ L.schemeNsmul n = L.schemeNsmul n)
    (U : A.affineOpens) :
    Function.Bijective (fun a : Γ(A, U.1) => a • L.eigenOne n hG U.1) := by sorry
