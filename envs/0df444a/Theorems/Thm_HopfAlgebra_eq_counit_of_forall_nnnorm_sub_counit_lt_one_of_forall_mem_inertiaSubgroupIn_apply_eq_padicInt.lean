-- Prove2me | Theorems.Thm_HopfAlgebra_eq_counit_of_forall_nnnorm_sub_counit_lt_one_of_forall_mem_inertiaSubgroupIn_apply_eq_padicInt
-- name    : HopfAlgebra.eq_counit_of_forall_nnnorm_sub_counit_lt_one_of_forall_mem_inertiaSubgroupIn_apply_eq_padicInt
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:55.342414+00:00
-- url     : https://prove2.me/theorems/493c985c-4f37-51fa-b123-80477e800fca
-- title:
--   Inertia-fixed identity-reducing ℚ̄ₚ-points are trivial
-- statement:
--   Let $p$ be a prime with $p \neq 2$, and let $H$ be a commutative ring carrying a Hopf algebra structure over $\mathbb{Z}_p$ which is finite and flat as a $\mathbb{Z}_p$-module and whose comultiplication is cocommutative. Let $f \colon H \to \overline{\mathbb{Q}}_p$ be a homomorphism of $\mathbb{Z}_p$-algebras into `PadicAlgCl p`, subject to two conditions. First, $f$ reduces to the counit: for every $h \in H$ the norm $\lVert f(h) - \varepsilon(h) \rVert$ is $< 1$, where $\varepsilon =$ `Coalgebra.counit` and its value is viewed in `PadicAlgCl p` through the structure map of $\mathbb{Z}_p$. Second, $f$ is fixed by inertia: writing $A$ for the valuation subring [`padicIntegers p`](def/GaloisRep_CompletionBridge.html#L20) of the valuation on `PadicAlgCl p`, every $\sigma$ in the subgroup of $\mathbb{Q}_p$-algebra automorphisms of `PadicAlgCl p` obtained as the image of the inertia subgroup of $A$ over $\mathbb{Q}_p$ under the inclusion of the decomposition subgroup satisfies $\sigma(f(h)) = f(h)$ for all $h \in H$. The conclusion is that $f$ coincides with the counit algebra homomorphism `Bialgebra.counitAlgHom` followed by the structure map $\mathbb{Z}_p \to$ `PadicAlgCl p`.
--
--   In the language of the finite flat commutative group scheme $G = \operatorname{Spec} H$ over $\mathbb{Z}_p$, this says that a $\overline{\mathbb{Q}}_p$-point of $G$ which reduces to the identity and is fixed by inertia is the identity point, i.e. $G^{0}(\overline{\mathbb{Q}}_p)^{I_p} = 0$; it is the rigidity available over an absolutely unramified base with $p$ odd, going back to Raynaud and Fontaine. It is used by [`HopfAlgebra.mem_of_forall_nnnorm_sub_counit_lt_one_of_forall_inertia_displacement_mem_padicInt`](thm.html#HopfAlgebra.mem_of_forall_nnnorm_sub_counit_lt_one_of_forall_inertia_displacement_mem_padicInt).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_HopfAlgebra_eq_counit_of_forall_nnnorm_sub_counit_lt_one_of_forall_mem_inertiaSubgroupIn_apply_eq_padicInt.lean

import Mathlib
import Definitions.Def_GaloisRep_CompletionBridge
import Definitions.Def_FLTPrelim_Ramification

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped PadicInt

theorem HopfAlgebra.eq_counit_of_forall_nnnorm_sub_counit_lt_one_of_forall_mem_inertiaSubgroupIn_apply_eq_padicInt
    (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2)
    (H : Type) [CommRing H] [HopfAlgebra ℤ_[p] H] [Module.Finite ℤ_[p] H] [Module.Flat ℤ_[p] H]
    [Coalgebra.IsCocomm ℤ_[p] H]
    (f : H →ₐ[ℤ_[p]] PadicAlgCl p)
    (hred : ∀ h : H, ‖f h - algebraMap ℤ_[p] (PadicAlgCl p) (Coalgebra.counit h)‖₊ < 1)
    (hfix : ∀ σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p, σ ∈ (padicIntegers p).inertiaSubgroupIn ℚ_[p] →
      ∀ h : H, σ (f h) = f h) :
    f = (Algebra.ofId ℤ_[p] (PadicAlgCl p)).comp (Bialgebra.counitAlgHom ℤ_[p] H) := by sorry
