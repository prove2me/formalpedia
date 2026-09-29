-- Prove2me | Theorems.Thm_HopfAlgebra_act_eq_nsmul_of_inertiaCyclotomicChain_padicInt
-- name    : HopfAlgebra.act_eq_nsmul_of_inertiaCyclotomicChain_padicInt
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:55.342414+00:00
-- url     : https://prove2.me/theorems/06b83935-dad3-5ebf-bb50-a5650a794e87
-- title:
--   Cyclotomic filtration forces inertia to act by ω (p odd)
-- statement:
--   Let $p$ be a prime with $p \neq 2$, and let $H$ be a commutative ring that is a cocommutative Hopf algebra over $\mathbb{Z}_p$, module-finite and flat over $\mathbb{Z}_p$. Let $M$ be an additive abelian group all of whose elements satisfy $p \cdot x = 0$, and let $e$ be a bijection from the convolution monoid `WithConv` of $\mathbb{Z}_p$-algebra homomorphisms $H \to$ `PadicAlgCl p` onto $M$ carrying the convolution product to addition, $e(fg) = e(f)+e(g)$. Let $\mathrm{act}$ assign to each $\mathbb{Q}_p$-algebra automorphism $\sigma$ of `PadicAlgCl p` a self-map of $M$, compatibly with $e$ in the relational sense: whenever $f,g$ are points with $g(h) = \sigma(f(h))$ for all $h \in H$, one has $e(g) = \mathrm{act}\,\sigma\,(e(f))$. Let $N_0, \dots, N_n$ be additive subgroups of $M$ with $N_0 = \bot$, $N_n = \top$, $N_i \le N_{i+1}$ for all $i$, each $N_i$ stable under every $\mathrm{act}\,\sigma$, and such that every step is cyclotomic for inertia: for $i < n$, for $\sigma$ in the image of the inertia subgroup of the valuation subring of `PadicAlgCl p` over $\mathbb{Q}_p$ inside the full automorphism group, and for every $c \in \mathbb{N}$ with $\sigma\zeta = \zeta^c$ for all $\zeta$ with $\zeta^p = 1$, one has $\mathrm{act}\,\sigma\,(x) - c \cdot x \in N_i$ for all $x \in N_{i+1}$. The conclusion is that for every such inertial $\sigma$ and every such $c$, $\mathrm{act}\,\sigma\,(x) = c \cdot x$ for all $x \in M$.
--
--   This is the local statement that a finite flat $\mathbb{Z}_p$-group scheme killed by $p$, with $p$ odd, whose geometric points form a successive extension of copies of $\mu_p$ as an inertia module, has inertia acting throughout by the mod $p$ cyclotomic character; the proof passes to the Cartier dual, where the dual filtration has inertia-trivial steps, and invokes [`HopfAlgebra.act_eq_self_of_inertiaTrivialChain_padicInt`](thm.html#HopfAlgebra.act_eq_self_of_inertiaTrivialChain_padicInt) together with the separation of points of $M$ by characters. It feeds the combined unramified-or-cyclotomic statement [`HopfAlgebra.inertia_displacement_eq_nsmul_of_inertiaTrivialOrCyclotomicChain_padicInt`](thm.html#HopfAlgebra.inertia_displacement_eq_nsmul_of_inertiaTrivialOrCyclotomicChain_padicInt).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_HopfAlgebra_act_eq_nsmul_of_inertiaCyclotomicChain_padicInt.lean

import Mathlib
import Definitions.Def_GaloisRep_CompletionBridge
import Definitions.Def_FLTPrelim_Ramification

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem HopfAlgebra.act_eq_nsmul_of_inertiaCyclotomicChain_padicInt
    (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2)
    (H : Type) [CommRing H] [HopfAlgebra ℤ_[p] H] [Module.Finite ℤ_[p] H] [Module.Flat ℤ_[p] H]
    [Coalgebra.IsCocomm ℤ_[p] H]
    (M : Type) [AddCommGroup M] (hM : ∀ x : M, p • x = 0)
    (e : WithConv (H →ₐ[ℤ_[p]] PadicAlgCl p) ≃ M) (he : ∀ f g, e (f * g) = e f + e g)
    (act : (PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) → M → M)
    (hact : ∀ (σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) (f g : WithConv (H →ₐ[ℤ_[p]] PadicAlgCl p)),
      (∀ h : H, g h = σ (f h)) → e g = act σ (e f))
    (n : ℕ) (N : Fin (n + 1) → AddSubgroup M)
    (hbot : N 0 = ⊥) (htop : N (Fin.last n) = ⊤) (hmono : ∀ i : Fin n, N i.castSucc ≤ N i.succ)
    (hstab : ∀ (i : Fin (n + 1)) (σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) (x : M),
      x ∈ N i → act σ x ∈ N i)
    (hstep : ∀ i : Fin n,
      ∀ σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p, σ ∈ (padicIntegers p).inertiaSubgroupIn ℚ_[p] →
        ∀ c : ℕ, (∀ ζ : PadicAlgCl p, ζ ^ p = 1 → σ ζ = ζ ^ c) →
          ∀ x ∈ N i.succ, act σ x - c • x ∈ N i.castSucc) :
    ∀ σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p, σ ∈ (padicIntegers p).inertiaSubgroupIn ℚ_[p] →
      ∀ c : ℕ, (∀ ζ : PadicAlgCl p, ζ ^ p = 1 → σ ζ = ζ ^ c) →
        ∀ x : M, act σ x = c • x := by sorry
