-- Prove2me | Theorems.Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_exists_affSES_filtration_pushforwardUnit_schemeNsmul
-- name    : GoodReductionJacobian.AbelianSchemePropertyBundle.exists_affSES_filtration_pushforwardUnit_schemeNsmul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:49.54035+00:00
-- url     : https://prove2.me/theorems/a780a868-57c6-564c-baff-6e1db5b0aab1
-- title:
--   Filtration of [n]_*mathcal O_A by n-torsion invertible modules
-- statement:
--   Let $K$ be an algebraically closed field, $A$ a scheme and $f : A \to \operatorname{Spec} K$, let $L$ be a relative group law on $f$ (a functorial group structure on the sets $\{\varphi : T \to A \mid \varphi \circ f = t\}$ of $T$-points over $\operatorname{Spec} K$, natural in $T$), assume $L$ commutative, assume the bundle `AbelianSchemePropertyBundle K f`, i.e. $f$ is smooth and proper, every fibre $f^{-1}(s)$ is connected and $f$ carries some relative group law, assume $f$ smooth of relative dimension $g$, and let $n$ be a natural number with $n \ne 0$ in $K$. Write $[n] :=$ `L.schemeNsmul n` $: A \to A$ for the endomorphism obtained by $n$-fold addition of the identity point. Then there exist families $E : \mathbb N \to$ `OModulePresheaf f` (data assigning to each open $U \subseteq A$ a $K$-module which is also a $\Gamma(A,U)$-module compatibly, together with restriction maps) and $M : \mathbb N \to A$`.Modules` such that $E_0$ is the zero presheaf, $E_{n^{2g}}$ is the pushforward along $[n]$ of the structure presheaf, $U \mapsto \Gamma(A, [n]^{-1}U)$, and for every $j < n^{2g}$: $M_j$ is invertible (each point of $A$ has an open neighbourhood $U$ with the pullback of $M_j$ to $U$ isomorphic to the unit sheaf of modules on $U$), the $n$-fold tensor power $M_j^{\otimes n}$ is isomorphic to the monoidal unit, and there is a sequence $0 \to E_j \to E_{j+1} \to$ `ofModules f` $M_j \to 0$ which on every affine open $U$ consists of $K$-linear, $\Gamma(A,U)$-semilinear maps compatible with restriction and is injective, surjective and exact at the middle term.
--
--   This is the statement that, for $n$ invertible in $K$, the pushforward $[n]_*\mathcal O_A$ along multiplication by $n$ on an abelian variety admits a filtration of length $n^{2g}$ whose graded pieces are invertible modules killed by $n$ in the Picard group — the eigen-decomposition for the translation action of $A[n](K)$, recorded here in the weaker filtered form and at the level of presheaves of modules on affine opens. It is used to compute the Euler characteristic of a pullback along $[n]$, in [`GoodReductionJacobian.AbelianSchemePropertyBundle.eulerChar_pullback_schemeNsmul_eq_pow_mul_eulerChar`](thm.html#GoodReductionJacobian.AbelianSchemePropertyBundle.eulerChar_pullback_schemeNsmul_eq_pow_mul_eulerChar).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_exists_affSES_filtration_pushforwardUnit_schemeNsmul.lean

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
import Definitions.Def_AlgebraicGeometry_OModulePresheafHom
import Definitions.Def_AlgebraicGeometry_OModulePresheafConstructions

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian

universe u

theorem GoodReductionJacobian.AbelianSchemePropertyBundle.exists_affSES_filtration_pushforwardUnit_schemeNsmul
    (K : Type u) [Field K] [IsAlgClosed K] {A : Scheme.{u}} (f : A ⟶ Spec (CommRingCat.of K))
    (L : RelativeGroupLaw K f) (hc : L.IsCommutative) (hA : AbelianSchemePropertyBundle K f)
    (g : ℕ) [SmoothOfRelativeDimension g f]
    (n : ℕ) (hn : (n : K) ≠ 0) :
    ∃ (E : ℕ → OModulePresheaf f) (M : ℕ → A.Modules),
      E 0 = OModulePresheaf.zero f ∧
      E (n ^ (2 * g)) = OModulePresheaf.pushforwardUnit f (L.schemeNsmul n) ∧
      ∀ j : ℕ, j < n ^ (2 * g) →
        Scheme.Modules.IsInvertible (M j) ∧ Nonempty ((M j).tensorPow n ≅ 𝟙_ (A.Modules)) ∧
        Nonempty (OModulePresheaf.AffSES (E j) (E (j + 1)) (OModulePresheaf.ofModules f (M j))) := by sorry
