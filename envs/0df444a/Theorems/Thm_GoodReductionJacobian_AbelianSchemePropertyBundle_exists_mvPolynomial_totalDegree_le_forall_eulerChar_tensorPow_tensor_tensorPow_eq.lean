-- Prove2me | Theorems.Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_exists_mvPolynomial_totalDegree_le_forall_eulerChar_tensorPow_tensor_tensorPow_eq
-- name    : GoodReductionJacobian.AbelianSchemePropertyBundle.exists_mvPolynomial_totalDegree_le_forall_eulerChar_tensorPow_tensor_tensorPow_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:49.54035+00:00
-- url     : https://prove2.me/theorems/3a1dd94b-648c-5538-928e-9cbf92e5ef27
-- title:
--   Two-variable Snapper polynomial for χ(M₀^{⊗ a}⊗ M₁^{⊗ b})
-- statement:
--   Let $K$ be an algebraically closed field, $A$ a scheme and $f : A \to \operatorname{Spec} K$ a morphism, equipped with: a term `L` of `RelativeGroupLaw K f`, i.e. a functorial group structure on the sets $\{\varphi : T \to A \mid \varphi \circ f = t\}$ of $A$-points over each $K$-scheme $t : T \to \operatorname{Spec} K$, with multiplication, unit and inverse satisfying associativity, unit and inverse laws and compatible with base change along $\psi : T' \to T$ over $\operatorname{Spec} K$; a term `hA` of `AbelianSchemePropertyBundle K f`, asserting that $f$ is smooth and proper, that every fibre $f^{-1}(s)$ is connected, and that a relative group law on $f$ exists; and, for a natural number $g$, the instance that $f$ is smooth of relative dimension $g$. Let $\mathcal{K}$ be an ordered affine cover of $A$, that is, a finite linearly ordered index family of affine opens whose supremum is $\top$, and let $M_0, M_1$ be $\mathcal{O}_A$-modules, each invertible in the sense that every point of $A$ has an open neighbourhood $U$ on which the pullback along $U \hookrightarrow A$ is isomorphic to the unit sheaf of modules of $U$. Then there is $P \in \mathbb{Q}[x_0,x_1]$ of total degree at most $g$ such that for all $a, b \in \mathbb{N}$ the Euler characteristic of the presheaf of $K$-module sections of $M_0^{\otimes a} \otimes M_1^{\otimes b}$ relative to $\mathcal{K}$ — the alternating sum $\sum_{i < \#\mathcal{K}.\iota} (-1)^i$ times the $K$-dimension of the $i$-th Čech module — equals $P(a,b)$, where the tensor powers are the iterated monoidal products built from the unit object.
--
--   This is the Snapper–Kleiman numerical polynomial in two variables, specialised to an abelian variety of dimension $g$ over an algebraically closed field: the Euler characteristic of $M_0^{\otimes a} \otimes M_1^{\otimes b}$ is a rational polynomial in $(a,b)$ of total degree at most $g$. It feeds the one-variable degree and leading-coefficient statements for tensor powers used in the intersection-theoretic input to the good-reduction analysis of Jacobians.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_exists_mvPolynomial_totalDegree_le_forall_eulerChar_tensorPow_tensor_tensorPow_eq.lean

import Mathlib
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawKernel
import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension
import Definitions.Def_AlgebraicGeometry_RelativeGroupLawEndDegree
import Definitions.Def_SheafOfModules_MonoidalV2
import Definitions.Def_AlgebraicGeometry_ModulesTensorPowV2
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_OModulePresheafEulerChar
import Definitions.Def_AlgebraicGeometry_OModulePresheafOfModules

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian

universe u

theorem GoodReductionJacobian.AbelianSchemePropertyBundle.exists_mvPolynomial_totalDegree_le_forall_eulerChar_tensorPow_tensor_tensorPow_eq
    (K : Type u) [Field K] [IsAlgClosed K] {A : Scheme.{u}} (f : A ⟶ Spec (CommRingCat.of K))
    (L : RelativeGroupLaw K f) (hA : AbelianSchemePropertyBundle K f)
    (g : ℕ) [SmoothOfRelativeDimension g f]
    (𝒦 : A.OrderedAffineCover) (M₀ M₁ : A.Modules)
    (h₀ : Scheme.Modules.IsInvertible M₀) (h₁ : Scheme.Modules.IsInvertible M₁) :
    ∃ P : MvPolynomial (Fin 2) ℚ, P.totalDegree ≤ g ∧
      ∀ a b : ℕ, (((OModulePresheaf.ofModules f (M₀.tensorPow a ⊗ M₁.tensorPow b)).eulerChar 𝒦 : ℤ) : ℚ) =
        MvPolynomial.eval ![(a : ℚ), (b : ℚ)] P := by sorry
