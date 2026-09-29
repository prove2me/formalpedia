-- Prove2me | Theorems.Thm_HopfAlgebra_mem_of_forall_nnnorm_sub_counit_lt_one_of_forall_inertia_displacement_mem_padicInt
-- name    : HopfAlgebra.mem_of_forall_nnnorm_sub_counit_lt_one_of_forall_inertia_displacement_mem_padicInt
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:57.239308+00:00
-- url     : https://prove2.me/theorems/9d7b1559-425f-5585-8d55-0b5bd58a9378
-- title:
--   Identity-reducing points lie in the inertia-displacement subgroup
-- statement:
--   Let $p$ be a prime with $p \neq 2$, and let $H$ be a commutative ring which is a cocommutative Hopf algebra over $\mathbb{Z}_p$, finite and flat as a $\mathbb{Z}_p$-module. Let $M$ be an additive commutative group together with a bijection $e$ from the convolution group $\mathtt{WithConv}(H \to_{\mathrm{alg}[\mathbb{Z}_p]} \mathtt{PadicAlgCl}\,p)$ of $\mathbb{Z}_p$-algebra homomorphisms $H \to \mathtt{PadicAlgCl}\,p$ onto $M$ satisfying $e(fg) = e(f) + e(g)$, and let $\mathrm{act}$ be an action of the group of $\mathbb{Q}_p$-algebra automorphisms of $\mathtt{PadicAlgCl}\,p$ on $M$ compatible with $e$ in the relational sense: whenever $\sigma$ is such an automorphism and $f, g$ are algebra homomorphisms with $g(h) = \sigma(f(h))$ for all $h \in H$, then $e(g) = \mathrm{act}\,\sigma\,(e(f))$. Let $W$ be an additive subgroup of $M$ containing all inertia displacements, i.e. $\mathrm{act}\,\sigma\,(x) - x \in W$ for every $x \in M$ and every $\sigma$ lying in the image, under the inclusion of the decomposition subgroup, of the inertia subgroup over $\mathbb{Q}_p$ of the valuation subring $\mathtt{padicIntegers}\,p$ attached to the valuation of $\mathtt{PadicAlgCl}\,p$. Then for every $f$ with $\|f(h) - \varepsilon(h)\|_{+} < 1$ for all $h \in H$, where $\varepsilon$ is the counit of $H$ composed with the structure map $\mathbb{Z}_p \to \mathtt{PadicAlgCl}\,p$, one has $e(f) \in W$.
--
--   In the language of finite flat commutative group schemes $G = \operatorname{Spec} H$ over $\mathbb{Z}_p$ with $p$ odd, this says that every point of $G(\overline{\mathbb{Q}}_p)$ reducing to the identity of the special fibre lies in any subgroup of the point group containing all displacements $\sigma x - x$ for $\sigma$ in inertia; equivalently the connected part of $G$ is absorbed by the inertia displacements. It is the group-theoretic input used by [`HopfAlgebra.act_eq_self_of_inertiaTrivialChain_padicInt`](thm.html#HopfAlgebra.act_eq_self_of_inertiaTrivialChain_padicInt) and [`HopfAlgebra.inertia_displacement_eq_nsmul_of_inertiaTrivialOrCyclotomicChain_padicInt`](thm.html#HopfAlgebra.inertia_displacement_eq_nsmul_of_inertiaTrivialOrCyclotomicChain_padicInt), and rests on the rigidity statement [`HopfAlgebra.eq_counit_of_forall_nnnorm_sub_counit_lt_one_of_forall_mem_inertiaSubgroupIn_apply_eq_padicInt`](thm.html#HopfAlgebra.eq_counit_of_forall_nnnorm_sub_counit_lt_one_of_forall_mem_inertiaSubgroupIn_apply_eq_padicInt) together with the construction of Galois-stable flat quotients.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_HopfAlgebra_mem_of_forall_nnnorm_sub_counit_lt_one_of_forall_inertia_displacement_mem_padicInt.lean

import Mathlib
import Definitions.Def_GaloisRep_CompletionBridge
import Definitions.Def_FLTPrelim_Ramification

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem HopfAlgebra.mem_of_forall_nnnorm_sub_counit_lt_one_of_forall_inertia_displacement_mem_padicInt
    (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2)
    (H : Type) [CommRing H] [HopfAlgebra ℤ_[p] H] [Module.Finite ℤ_[p] H] [Module.Flat ℤ_[p] H]
    [Coalgebra.IsCocomm ℤ_[p] H]
    (M : Type) [AddCommGroup M]
    (e : WithConv (H →ₐ[ℤ_[p]] PadicAlgCl p) ≃ M) (he : ∀ f g, e (f * g) = e f + e g)
    (act : (PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) → M → M)
    (hact : ∀ (σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) (f g : WithConv (H →ₐ[ℤ_[p]] PadicAlgCl p)),
      (∀ h : H, g h = σ (f h)) → e g = act σ (e f))
    (W : AddSubgroup M)
    (hW : ∀ σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p, σ ∈ (padicIntegers p).inertiaSubgroupIn ℚ_[p] →
      ∀ x : M, act σ x - x ∈ W)
    (f : WithConv (H →ₐ[ℤ_[p]] PadicAlgCl p))
    (hred : ∀ h : H, ‖f h - algebraMap ℤ_[p] (PadicAlgCl p) (Coalgebra.counit (R := ℤ_[p]) h)‖₊ < 1) :
    e f ∈ W := by sorry
