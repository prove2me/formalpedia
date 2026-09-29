-- Prove2me | Theorems.Thm_HopfAlgebra_act_eq_self_of_inertiaTrivialChain_padicInt
-- name    : HopfAlgebra.act_eq_self_of_inertiaTrivialChain_padicInt
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:55.342414+00:00
-- url     : https://prove2.me/theorems/5e548b5b-e844-5512-9ca7-6ba545f9d548
-- title:
--   Inertia acts trivially on a finite flat ℤₚ-group with unramified chain (p odd)
-- statement:
--   Let $p$ be a prime with $p \neq 2$, and let $H$ be a commutative ring which is a cocommutative Hopf algebra over $\mathbb{Z}_p$, module-finite and flat over $\mathbb{Z}_p$. Let $M$ be an additive abelian group and $e$ a bijection from $\mathrm{Hom}_{\mathbb{Z}_p\text{-alg}}(H, \overline{\mathbb{Q}}_p)$, equipped with its convolution monoid structure (`WithConv`), onto $M$ with $e(fg) = e(f) + e(g)$ for all $f,g$; here $\overline{\mathbb{Q}}_p$ is `PadicAlgCl p`. Let $\mathrm{act}$ assign to each $\sigma \in \overline{\mathbb{Q}}_p \simeq_{\mathbb{Q}_p} \overline{\mathbb{Q}}_p$ a map $M \to M$, compatibly with $e$ in the relational sense that whenever $f, g$ are points with $g(h) = \sigma(f(h))$ for all $h \in H$, one has $e(g) = \mathrm{act}\,\sigma\,(e(f))$. Let $n \in \mathbb{N}$ and let $N_0, \dots, N_n$ be additive subgroups of $M$ with $N_0 = \bot$, $N_n = \top$, and $N_i \le N_{i+1}$ for all $i$, each $N_i$ stable under every $\mathrm{act}\,\sigma$. Write $I_p$ for the inertia subgroup of the valuation subring of $\overline{\mathbb{Q}}_p$ attached to the valuation `Valued.v`, transported into $\overline{\mathbb{Q}}_p \simeq_{\mathbb{Q}_p} \overline{\mathbb{Q}}_p$ along the inclusion of the decomposition subgroup. Assume that for each $i$, each $\sigma \in I_p$ and each $x \in N_{i+1}$ one has $\mathrm{act}\,\sigma\,(x) - x \in N_i$. Then $\mathrm{act}\,\sigma\,(x) = x$ for every $\sigma \in I_p$ and every $x \in M$.
--
--   This is the statement that a finite flat commutative group scheme over $\mathbb{Z}_p$, $p$ odd, whose $\overline{\mathbb{Q}}_p$-points form a successive extension of Galois modules on which inertia acts trivially, has unramified generic fibre — the dévissage form of the fact that an extension of étale finite flat groups over an odd $p$-adic base is étale, with the group of points presented abstractly through the bijection $e$. It is used in the cyclotomic variant [`HopfAlgebra.act_eq_nsmul_of_inertiaCyclotomicChain_padicInt`](thm.html#HopfAlgebra.act_eq_nsmul_of_inertiaCyclotomicChain_padicInt), which supplies the local information at $p$ needed for the ramification analysis of the Galois representations occurring in the argument.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_HopfAlgebra_act_eq_self_of_inertiaTrivialChain_padicInt.lean

import Mathlib
import Definitions.Def_GaloisRep_CompletionBridge
import Definitions.Def_FLTPrelim_Ramification

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem HopfAlgebra.act_eq_self_of_inertiaTrivialChain_padicInt
    (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2)
    (H : Type) [CommRing H] [HopfAlgebra ℤ_[p] H] [Module.Finite ℤ_[p] H] [Module.Flat ℤ_[p] H]
    [Coalgebra.IsCocomm ℤ_[p] H]
    (M : Type) [AddCommGroup M]
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
        ∀ x ∈ N i.succ, act σ x - x ∈ N i.castSucc) :
    ∀ σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p, σ ∈ (padicIntegers p).inertiaSubgroupIn ℚ_[p] →
      ∀ x : M, act σ x = x := by sorry
