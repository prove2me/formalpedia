-- Prove2me | Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_nonempty_pullback_schemeNsmul_iso_tensorPow_tensor_pullback_inv_tensorPow_monoidalV2
-- name    : GoodReductionJacobian.RelativeGroupLaw.nonempty_pullback_schemeNsmul_iso_tensorPow_tensor_pullback_inv_tensorPow_monoidalV2
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:53.637625+00:00
-- url     : https://prove2.me/theorems/ac9cda4d-540b-5128-b4c6-d59ca600a8d9
-- title:
--   Mumford's formula for [n]^*L on an abelian scheme
-- statement:
--   Fix an algebraically closed field $K$, a scheme $A$ and a morphism $f : A \to \operatorname{Spec} K$. Assume given a relative group law $L$ for $f$, that is, operations $\mathrm{mul}$, $\mathrm{one}$, $\mathrm{inv}$ on the sets $\{\varphi : T \to A \mid \varphi \circ f = t\}$ of $A$-valued points over each $K$-scheme $t : T \to \operatorname{Spec} K$, satisfying associativity, the two unit laws, the left inverse law, and naturality of multiplication under base change along morphisms $\psi : T' \to T$ over $\operatorname{Spec} K$. Assume $L$ is commutative ($\mathrm{mul}$ is symmetric on all $T$-points), and that $f$ carries the property bundle `AbelianSchemePropertyBundle`: $f$ is smooth, proper, every fibre $f^{-1}(s)$ is connected, and a relative group law for $f$ exists. Let $\mathcal{L}$ be an object of `A.Modules` which is invertible, in the sense that every point of $A$ has an open neighbourhood $U$ such that the pullback of $\mathcal{L}$ along $U \hookrightarrow A$ is isomorphic to the unit module on $U$, and let $n$ be a natural number. Write $[n] : A \to A$ for the underlying morphism of the $n$-fold power of the identity point under $\mathrm{mul}$ (starting from $\mathrm{one}$), and $[-1] : A \to A$ for the underlying morphism of the inverse of the identity point. The conclusion asserts that the type of isomorphisms
--   $$[n]^*\mathcal{L} \;\cong\; \mathcal{L}^{\otimes (n^2+n)/2} \otimes \bigl([-1]^*\mathcal{L}\bigr)^{\otimes (n^2-n)/2}$$
--   in `A.Modules` is nonempty, where tensor powers are formed by iterated tensoring on the right starting from the unit object, and the exponents use natural-number division and truncated subtraction.
--
--   This is Mumford's formula for the pullback of a line bundle along multiplication by $n$ on an abelian variety, a standard consequence of the theorem of the cube, here in the formulation for a scheme over an algebraically closed field equipped with a relative group law. It feeds the companion statement [`GoodReductionJacobian.RelativeGroupLaw.nonempty_pullback_schemeNsmul_tensorPow_tensor_tensorPow_iso_monoidalV2`](thm.html#GoodReductionJacobian.RelativeGroupLaw.nonempty_pullback_schemeNsmul_tensorPow_tensor_tensorPow_iso_monoidalV2), the proof combining the cube isomorphism, the existence of tensor inverses for invertible modules, and an arithmetic identity for cube-type functions on abelian groups.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GoodReductionJacobian_RelativeGroupLaw_nonempty_pullback_schemeNsmul_iso_tensorPow_tensor_pullback_inv_tensorPow_monoidalV2.lean

import Mathlib
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawKernel
import Definitions.Def_SheafOfModules_MonoidalV2
import Definitions.Def_AlgebraicGeometry_ModulesTensorPowV2
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian

universe u

theorem GoodReductionJacobian.RelativeGroupLaw.nonempty_pullback_schemeNsmul_iso_tensorPow_tensor_pullback_inv_tensorPow_monoidalV2
    (K : Type u) [Field K] [IsAlgClosed K] {A : Scheme.{u}} (f : A ⟶ Spec (CommRingCat.of K))
    (L : RelativeGroupLaw K f) (hc : L.IsCommutative) (hA : AbelianSchemePropertyBundle K f)
    (𝓛 : A.Modules) (h𝓛 : Scheme.Modules.IsInvertible 𝓛) (n : ℕ) :
    Nonempty ((Scheme.Modules.pullback (L.schemeNsmul n)).obj 𝓛 ≅
      𝓛.tensorPow ((n * n + n) / 2) ⊗
        ((Scheme.Modules.pullback (L.inv f ⟨𝟙 A, Category.id_comp f⟩).1).obj 𝓛).tensorPow ((n * n - n) / 2)) := by sorry
