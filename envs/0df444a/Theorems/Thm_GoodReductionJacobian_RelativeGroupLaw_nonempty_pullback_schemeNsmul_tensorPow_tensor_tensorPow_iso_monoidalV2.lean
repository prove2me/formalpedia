-- Prove2me | Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_nonempty_pullback_schemeNsmul_tensorPow_tensor_tensorPow_iso_monoidalV2
-- name    : GoodReductionJacobian.RelativeGroupLaw.nonempty_pullback_schemeNsmul_tensorPow_tensor_tensorPow_iso_monoidalV2
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:53.637625+00:00
-- url     : https://prove2.me/theorems/2e17f991-1e2e-554b-ad90-f93d623c7f2b
-- title:
--   Pull-back along [n] of M^{⊗ a}⊗([-1]^*M)^{⊗ b}
-- statement:
--   Let $K$ be an algebraically closed field and let $f : A \to \operatorname{Spec} K$ be a morphism of schemes. Let $L$ be a `RelativeGroupLaw` for $f$, that is, a functorial group structure on the sets $\{\varphi : T \to A \mid \varphi \circ f = t\}$ of $T$-points over $\operatorname{Spec} K$ (multiplication, unit and inversion for every $t : T \to \operatorname{Spec} K$, with associativity, the two unit laws, left inverse, and naturality of multiplication under base change along $\psi : T' \to T$), assumed commutative by `hc`; `hA` asserts that $f$ is smooth and proper, that each fibre of $f$ over a point of $\operatorname{Spec} K$ is connected, and that some relative group law for $f$ exists. Let $M$ be an object of $A$-modules which is invertible in the sense that every point of $A$ has an open neighbourhood $U$ to which the restriction of $M$ is isomorphic to the unit module on $U$. Write $[n] =$ `L.schemeNsmul n` for the underlying morphism $A \to A$ of the $n$-fold $L$-sum of the identity point of $A$, and $[-1]$ for the underlying morphism of the $L$-inverse of that identity point. Then for all natural numbers $n, a, b$ the statement asserts that the set of isomorphisms $$[n]^*\bigl(M^{\otimes a} \otimes ([-1]^*M)^{\otimes b}\bigr) \;\cong\; M^{\otimes(\alpha a + \beta b)} \otimes ([-1]^*M)^{\otimes(\beta a + \alpha b)}$$ is nonempty, where $\alpha = (n^2+n)/2$, $\beta = (n^2-n)/2$ (natural-number division) and tensor powers are formed by the recursion $M^{\otimes 0} = \mathbf{1}$, $M^{\otimes(k+1)} = M^{\otimes k} \otimes M$.
--
--   This is the bigraded form of Mumford's formula $[n]^*\mathcal L \cong \mathcal L^{\otimes(n^2+n)/2} \otimes ([-1]^*\mathcal L)^{\otimes(n^2-n)/2}$ for line bundles on an abelian variety, extended from a single invertible module to the tensor products $M^{\otimes a} \otimes ([-1]^*M)^{\otimes b}$. It feeds the computation of Euler characteristics of tensor powers used in the study of the relative Picard functor of a Jacobian.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GoodReductionJacobian_RelativeGroupLaw_nonempty_pullback_schemeNsmul_tensorPow_tensor_tensorPow_iso_monoidalV2.lean

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

theorem GoodReductionJacobian.RelativeGroupLaw.nonempty_pullback_schemeNsmul_tensorPow_tensor_tensorPow_iso_monoidalV2
    (K : Type u) [Field K] [IsAlgClosed K] {A : Scheme.{u}} (f : A ⟶ Spec (CommRingCat.of K))
    (L : RelativeGroupLaw K f) (hc : L.IsCommutative) (hA : AbelianSchemePropertyBundle K f)
    (M : A.Modules) (hM : Scheme.Modules.IsInvertible M) (n a b : ℕ) :
    Nonempty ((Scheme.Modules.pullback (L.schemeNsmul n)).obj
        (M.tensorPow a ⊗ ((Scheme.Modules.pullback (L.inv f ⟨𝟙 A, Category.id_comp f⟩).1).obj M).tensorPow b) ≅
      M.tensorPow ((n * n + n) / 2 * a + (n * n - n) / 2 * b) ⊗
        ((Scheme.Modules.pullback (L.inv f ⟨𝟙 A, Category.id_comp f⟩).1).obj M).tensorPow
          ((n * n - n) / 2 * a + (n * n + n) / 2 * b)) := by sorry
