-- Prove2me | Theorems.Thm_IntMul_HvdH_lemma_2_3
-- name    : IntMul.HvdH.lemma_2_3
-- status  : Proved
-- author  : @avi
-- created : 2026-10-09T01:44:14.96383+00:00
-- url     : https://prove2.me/theorems/b64cce8f-dd3c-4b84-be18-18a96815d512
-- title:
--   HvdH Lemma 2.3 — convolution formula $\frac1n u*v = n\,\mathcal F_{\omega^{-1}}(\mathcal F_\omega u\cdot\mathcal F_\omega v)$
-- statement:
--   Let $R$ be a commutative $\mathbb C$-algebra, $n\ge1$, and $\omega\in R^\times$ with $\omega^n=1$ and $\sum_{k=0}^{n-1}(\omega^j)^k=0$ for every integer $j\not\equiv0\pmod n$. For $w\in R^\times$ define the DFT $\mathcal F_w:R^n\to R^n$ by
--   $$(\mathcal F_w x)_j=\frac1n\sum_{k=0}^{n-1}w^{-jk}x_k,\qquad 0\le j<n,$$
--   and the cyclic convolution $(u*v)_j=\sum_{k=0}^{n-1}u_kv_{j-k}$ (indices mod $n$). Then for all $u,v\in R^n$,
--   $$\frac1n\,u*v \;=\; n\,\mathcal F_{\omega^{-1}}\big(\mathcal F_\omega u\cdot\mathcal F_\omega v\big),$$
--   where $\cdot$ is the pointwise product.
--
--   Formalization note: vectors are functions `ZMod n → R`; the exponent $-jk$ uses the representatives $j,k\in\{0,\dots,n-1\}$. The paper's definition of a principal root also asks $\|\omega u\|=\|u\|$ for a norm on $R$; that condition plays no role in this lemma and is omitted, so the statement covers every commutative $\mathbb C$-algebra.
-- source:
--   D. Harvey, J. van der Hoeven, Integer multiplication in time O(n log n), Ann. of Math. 193 (2021), https://doi.org/10.4007/annals.2021.193.2.4 (preprint https://hal.science/hal-02070778v2), Lemma 2.3, p. 12 (with the definitions of principal root of unity, F_ω, u·v and u*v in §2.4, pp. 11–12).

import Mathlib

namespace IntMul.HvdH

theorem lemma_2_3 {R : Type*} [CommRing R] [Algebra ℂ R] (n : ℕ) [NeZero n] (ω : Rˣ)
    (hω : ω ^ n = 1)
    (hsum : ∀ j : ℤ, ¬ (n : ℤ) ∣ j → ∑ k ∈ Finset.range n, ((ω ^ j : Rˣ) : R) ^ k = 0)
    (u v : ZMod n → R) :
    let F : Rˣ → (ZMod n → R) → ZMod n → R := fun w x j =>
      (1 / (n : ℂ)) • ∑ k : ZMod n, ((w ^ (-((j.val * k.val : ℕ) : ℤ)) : Rˣ) : R) * x k
    (1 / (n : ℂ)) • (fun j => ∑ k : ZMod n, u k * v (j - k)) =
      (n : ℂ) • F ω⁻¹ (fun j => F ω u j * F ω v j) := by sorry

end IntMul.HvdH
