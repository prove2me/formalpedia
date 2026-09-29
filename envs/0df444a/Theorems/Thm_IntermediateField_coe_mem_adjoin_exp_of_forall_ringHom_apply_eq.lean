-- Prove2me | Theorems.Thm_IntermediateField_coe_mem_adjoin_exp_of_forall_ringHom_apply_eq
-- name    : IntermediateField.coe_mem_adjoin_exp_of_forall_ringHom_apply_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:57.515241+00:00
-- url     : https://prove2.me/theorems/1fc31081-7c4b-5c7b-a409-7ad794824eb6
-- title:
--   Elements of ℚ(ζ_N) fixed by s≡ 1 mod p lie in ℚ(ζₚ)
-- statement:
--   Let $N$ be a nonzero natural number and let $p$ be a natural number dividing $N$. Write $\zeta_N = \exp(2\pi i/N) \in \mathbb{C}$ and let $K = \mathbb{Q}(\zeta_N)$ be the intermediate field of $\mathbb{C}/\mathbb{Q}$ obtained by adjoining the single element $\zeta_N$. Let $z$ be an element of $K$ and assume: for every natural number $s$ coprime to $N$ with $s \equiv 1 \pmod p$, and every ring homomorphism $\varphi\colon K \to \mathbb{C}$ with the normalisation that $\varphi(w) = \zeta_N^{\,s}$ for every $w \in K$ whose image in $\mathbb{C}$ equals $\zeta_N$, one has $\varphi(z) = z$ (as elements of $\mathbb{C}$, $z$ being read through the inclusion $K \subseteq \mathbb{C}$). The conclusion is that the complex number underlying $z$ lies in the intermediate field $\mathbb{Q}(\exp(2\pi i/p))$ of $\mathbb{C}/\mathbb{Q}$. Note that $p$ is not assumed prime, only that it divides $N$.
--
--   This is the Galois-descent step for cyclotomic fields: under the identification $\mathrm{Gal}(\mathbb{Q}(\zeta_N)/\mathbb{Q}) \cong (\mathbb{Z}/N)^{\times}$, $\sigma_s(\zeta_N) = \zeta_N^{\,s}$, the automorphisms fixing $\zeta_p = \zeta_N^{N/p}$ are exactly those with $s \equiv 1 \pmod p$, so the fixed field of that subgroup is $\mathbb{Q}(\zeta_p)$. The hypothesis is formulated with ring homomorphisms into $\mathbb{C}$ normalised on $\zeta_N$, which is the form in which Galois conjugation arises for $q$-expansion coefficients; it is used to show that coefficients of the $q$-expansions attached to $\Gamma_1$-level structures lie in $\mathbb{Q}(\zeta_p)$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_IntermediateField_coe_mem_adjoin_exp_of_forall_ringHom_apply_eq.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem IntermediateField.coe_mem_adjoin_exp_of_forall_ringHom_apply_eq
    (N p : ℕ) [NeZero N] (hp : p ∣ N)
    (z : ↥(IntermediateField.adjoin ℚ ({Complex.exp (2 * (Real.pi : ℂ) * Complex.I / (N : ℂ))} : Set ℂ)))
    (hz : ∀ s : ℕ, s.Coprime N → s ≡ 1 [MOD p] →
      ∀ φ : ↥(IntermediateField.adjoin ℚ ({Complex.exp (2 * (Real.pi : ℂ) * Complex.I / (N : ℂ))} : Set ℂ)) →+* ℂ,
        (∀ w : ↥(IntermediateField.adjoin ℚ ({Complex.exp (2 * (Real.pi : ℂ) * Complex.I / (N : ℂ))} : Set ℂ)),
            (w : ℂ) = Complex.exp (2 * (Real.pi : ℂ) * Complex.I / (N : ℂ)) →
            φ w = Complex.exp (2 * (Real.pi : ℂ) * Complex.I / (N : ℂ)) ^ s) →
        φ z = z) :
    (z : ℂ) ∈ IntermediateField.adjoin ℚ ({Complex.exp (2 * (Real.pi : ℂ) * Complex.I / (p : ℂ))} : Set ℂ) := by sorry
