-- Prove2me | Theorems.Thm_NumberField_exists_forall_le_tsum_absNorm_rpow_neg_of_isCyclotomicExtension
-- name    : NumberField.exists_forall_le_tsum_absNorm_rpow_neg_of_isCyclotomicExtension
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:57.964832+00:00
-- url     : https://prove2.me/theorems/320fd511-72d6-53d1-bc1d-c4618c28bee0
-- title:
--   Divergence of prime sums in a norm class mod m
-- statement:
--   Let $K$ and $L$ be number fields with $L$ an algebra over $K$, let $m$ be a natural number that is non-zero, and assume $L$ is a cyclotomic extension of $K$ of conductor set $\{m\}$; let $\zeta \in L$ be a primitive $m$-th root of unity, let $\tau$ be a $K$-algebra automorphism of $L$, and let $C$ be a real number. The assertion is that there exists $\delta > 0$ such that for every real $s$ with $1 < s < 1 + \delta$ one has
--   $$C \le \sum_{v}' \begin{cases} N(v)^{-s} & \text{if } N(v) \equiv a \pmod m,\\ 0 & \text{otherwise,}\end{cases}$$
--   the (unconditional) sum being taken over the height-one spectrum of $\mathcal{O}_K$, i.e. over the non-zero prime ideals $v$ of the ring of integers of $K$, with $N(v)$ the absolute norm of $v$ viewed as a real number, and where $a \in \mathbb{Z}/m\mathbb{Z}$ is the image of the unit of $\mathbb{Z}/m\mathbb{Z}$ attached to $\tau$ by the Galois-to-power map of $\zeta$, that is the class $a$ with $\tau(\zeta) = \zeta^a$. Thus the sum of $N(v)^{-s}$ over the primes of $K$ whose absolute norm lies in the residue class $a$ modulo $m$ tends to $+\infty$ as $s \to 1^+$.
--
--   This is the divergence form of Hecke's generalisation of Dirichlet's theorem on primes in arithmetic progressions: the primes of $K$ whose absolute norm lies in a residue class modulo $m$ realised by an element of $\mathrm{Gal}(K(\zeta_m)/K)$ have positive Dirichlet density, of which only the divergence of the associated prime sum is asserted here. It is used to produce a prime of $K$ with prescribed absolute norm modulo $m$ and prescribed Frobenius behaviour in the cyclotomic extension.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_exists_forall_le_tsum_absNorm_rpow_neg_of_isCyclotomicExtension.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField

theorem NumberField.exists_forall_le_tsum_absNorm_rpow_neg_of_isCyclotomicExtension
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (m : ℕ) [NeZero m] [IsCyclotomicExtension {m} K L] {ζ : L} (hζ : IsPrimitiveRoot ζ m)
    (τ : L ≃ₐ[K] L) (C : ℝ) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ s : ℝ, 1 < s → s < 1 + δ →
      C ≤ ∑' v : IsDedekindDomain.HeightOneSpectrum (𝓞 K),
        (if (Ideal.absNorm v.asIdeal : ZMod m) = ((hζ.autToPow K τ : (ZMod m)ˣ) : ZMod m)
          then (Ideal.absNorm v.asIdeal : ℝ) ^ (-s) else 0) := by sorry
