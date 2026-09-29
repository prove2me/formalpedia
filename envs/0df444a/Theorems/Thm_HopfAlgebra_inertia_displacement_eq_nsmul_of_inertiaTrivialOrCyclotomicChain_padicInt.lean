-- Prove2me | Theorems.Thm_HopfAlgebra_inertia_displacement_eq_nsmul_of_inertiaTrivialOrCyclotomicChain_padicInt
-- name    : HopfAlgebra.inertia_displacement_eq_nsmul_of_inertiaTrivialOrCyclotomicChain_padicInt
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:56.883924+00:00
-- url     : https://prove2.me/theorems/0274a391-aba0-5c59-af2f-18ab585af0a5
-- title:
--   Inertia acts cyclotomically on inertia displacements (p odd)
-- statement:
--   Let $p$ be an odd prime and let $H$ be a commutative ring which is a Hopf algebra over $\mathbb{Z}_p$, module-finite and flat over $\mathbb{Z}_p$, with cocommutative comultiplication. Let $M$ be an additive abelian group killed by $p$ (every $x \in M$ satisfies $p \cdot x = 0$), let $e$ be a bijection from the set of $\mathbb{Z}_p$-algebra homomorphisms $H \to \mathrm{PadicAlgCl}\,p$ equipped with the convolution product (`WithConv`) onto $M$ carrying convolution to addition, $e(f * g) = e(f) + e(g)$, and let $\mathrm{act}$ be a map assigning to each $\mathbb{Q}_p$-algebra automorphism $\sigma$ of $\mathrm{PadicAlgCl}\,p$ a self-map of $M$ compatible with $e$, in the sense that if $g(h) = \sigma(f(h))$ for all $h \in H$ then $e(g) = \mathrm{act}\,\sigma\,(e f)$. Here inertia means membership in `(padicIntegers p).inertiaSubgroupIn ℚ_[p]`, the image in the full automorphism group of the inertia subgroup of the valuation subring of $\mathrm{PadicAlgCl}\,p$ attached to its valuation `Valued.v`, under the inclusion of the decomposition subgroup. Assume given $n$ and a family $N : \mathrm{Fin}(n+1) \to$ additive subgroups of $M$ with $N_0 = \bot$, $N_{\mathrm{last}} = \top$, $N_{i} \le N_{i+1}$ for each $i$, every $N_i$ stable under $\mathrm{act}\,\sigma$ for all $\sigma$, and, for each $i$, either: for all inertia $\sigma$ and all $x \in N_{i+1}$, $\mathrm{act}\,\sigma\,x - x \in N_i$; or: for all inertia $\sigma$, all $c \in \mathbb{N}$ with $\sigma\zeta = \zeta^c$ for every $\zeta$ with $\zeta^p = 1$, and all $x \in N_{i+1}$, $\mathrm{act}\,\sigma\,x - c \cdot x \in N_i$. The conclusion: for all inertia elements $\sigma, \tau$, every $c \in \mathbb{N}$ with $\tau\zeta = \zeta^c$ for all $\zeta$ with $\zeta^p = 1$, and every $x \in M$, one has $\mathrm{act}\,\tau\,(\mathrm{act}\,\sigma\,x - x) = c \cdot (\mathrm{act}\,\sigma\,x - x)$.
--
--   This is the statement that a finite flat $\mathbb{Z}_p$-group scheme with $p$-torsion $\overline{\mathbb{Q}}_p$-points filtered by unramified and cyclotomic Galois-stable pieces is multiplicative-by-étale over the inertia-invariants in the sense that inertia acts through the mod $p$ cyclotomic character on all displacements $\sigma x - x$; it is the local input at $p$ for passing from flatness to ordinarity. It is used by [`ResidualGaloisRep.exists_isOrdinaryCocycleAd_of_isLocallyFlatCocycleAd`](thm.html#ResidualGaloisRep.exists_isOrdinaryCocycleAd_of_isLocallyFlatCocycleAd).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_HopfAlgebra_inertia_displacement_eq_nsmul_of_inertiaTrivialOrCyclotomicChain_padicInt.lean

import Mathlib
import Definitions.Def_GaloisRep_CompletionBridge
import Definitions.Def_FLTPrelim_Ramification

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem HopfAlgebra.inertia_displacement_eq_nsmul_of_inertiaTrivialOrCyclotomicChain_padicInt
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
      (∀ σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p, σ ∈ (padicIntegers p).inertiaSubgroupIn ℚ_[p] →
        ∀ x ∈ N i.succ, act σ x - x ∈ N i.castSucc) ∨
      (∀ σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p, σ ∈ (padicIntegers p).inertiaSubgroupIn ℚ_[p] →
        ∀ c : ℕ, (∀ ζ : PadicAlgCl p, ζ ^ p = 1 → σ ζ = ζ ^ c) →
          ∀ x ∈ N i.succ, act σ x - c • x ∈ N i.castSucc)) :
    ∀ σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p, σ ∈ (padicIntegers p).inertiaSubgroupIn ℚ_[p] →
    ∀ τ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p, τ ∈ (padicIntegers p).inertiaSubgroupIn ℚ_[p] →
    ∀ c : ℕ, (∀ ζ : PadicAlgCl p, ζ ^ p = 1 → τ ζ = ζ ^ c) →
      ∀ x : M, act τ (act σ x - x) = c • (act σ x - x) := by sorry
