-- Prove2me | Theorems.Thm_NumberField_sum_mult_mul_log_one_add_norm_sq_add_two_mul_finsum_log_max_norm_le_of_one_sub_mul_eq_sum
-- name    : NumberField.sum_mult_mul_log_one_add_norm_sq_add_two_mul_finsum_log_max_norm_le_of_one_sub_mul_eq_sum
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:58.387243+00:00
-- url     : https://prove2.me/theorems/87c4fe1a-4f60-5b60-9d41-683af028190b
-- title:
--   Adelic height bound from a factorised identity (1-c)x=sumⱼ PⱼUⱼ
-- statement:
--   Let $F$ be a number field, $c\in F$ with $c\neq1$, $\ell$ a natural number, $x$ an element of the adele ring of $F$ (relative to $\mathcal O_F$), and $P,U,Q$ three sequences of adeles indexed by $\mathbb N$. Assume the two identities $(1-c)\,x=\sum_{j<\ell}P_j\,U_j$ and $c=\prod_{i<\ell}Q_i$ in the adele ring, where $1-c$ and $c$ are viewed adelically through the structure map from $F$. Let $W$ be a finite set of height-one primes of $\mathcal O_F$, and let $\Lambda$ on the height-one spectrum and $\Lambda_\infty$ on the infinite places be real-valued functions with $\Lambda_w\ge1$ for all $w$, $\Lambda_w=1$ for $w\notin W$, and $\Lambda_{\infty,w}\ge1$ for all $w$. Assume that for every $j<\ell$ each finite component of $P_j$ has norm at most $\Lambda_w$ at $w$ and each infinite component norm at most $\Lambda_{\infty,w}$, and likewise for $U_j$ and for $Q_i$ with $i<\ell$. Then, with $m_w$ the multiplicity of an infinite place ($1$ real, $2$ complex),
--   $$\sum_{w\mid\infty}m_w\log\bigl(1+\|x_w\|^2\bigr)+2\sum_{v}\log\max(1,\|x_v\|)\le(2\ell+4)\Bigl(\sum_{w\in W}\log\Lambda_w+\sum_{w\mid\infty}m_w\log\Lambda_{\infty,w}\Bigr)+(4\log2+2\log\ell)\sum_{w\mid\infty}m_w,$$
--   the sum over finite places being an unconditional sum of a function with finite support.
--
--   This is the local-to-global bookkeeping step bounding the adelic height of an adele $x$ which solves a factorised identity with coefficients of controlled local size, the control at the finite places being paid for by the product-formula inequality comparing $\sum\log^+\|1-c\|^{-1}$ with $\sum\log^+\|c\|$. It is used in the estimate for the adelic height and Weyl-type quantity attached to a double coset at which an automorphic form does not vanish.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_sum_mult_mul_log_one_add_norm_sq_add_two_mul_finsum_log_max_norm_le_of_one_sub_mul_eq_sum.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField IsDedekindDomain

theorem NumberField.sum_mult_mul_log_one_add_norm_sq_add_two_mul_finsum_log_max_norm_le_of_one_sub_mul_eq_sum
    (F : Type) [Field F] [NumberField F] (c : F) (hc : c ≠ 1) (ℓ : ℕ)
    (x : AdeleRing (𝓞 F) F) (P U Q : ℕ → AdeleRing (𝓞 F) F)
    (hx : algebraMap F (AdeleRing (𝓞 F) F) (1 - c) * x = ∑ j ∈ Finset.range ℓ, P j * U j)
    (hcQ : algebraMap F (AdeleRing (𝓞 F) F) c = ∏ i ∈ Finset.range ℓ, Q i)
    (W : Finset (HeightOneSpectrum (𝓞 F))) (Λ : HeightOneSpectrum (𝓞 F) → ℝ) (Λinf : InfinitePlace F → ℝ)
    (hΛ : ∀ w, 1 ≤ Λ w) (hΛW : ∀ w, w ∉ W → Λ w = 1) (hΛinf : ∀ w, 1 ≤ Λinf w)
    (hP : ∀ j, j < ℓ → (∀ w : HeightOneSpectrum (𝓞 F), ‖(P j).2 w‖ ≤ Λ w) ∧ ∀ w : InfinitePlace F, ‖(P j).1 w‖ ≤ Λinf w)
    (hU : ∀ j, j < ℓ → (∀ w : HeightOneSpectrum (𝓞 F), ‖(U j).2 w‖ ≤ Λ w) ∧ ∀ w : InfinitePlace F, ‖(U j).1 w‖ ≤ Λinf w)
    (hQ : ∀ i, i < ℓ → (∀ w : HeightOneSpectrum (𝓞 F), ‖(Q i).2 w‖ ≤ Λ w) ∧ ∀ w : InfinitePlace F, ‖(Q i).1 w‖ ≤ Λinf w) :
    (∑ w : InfinitePlace F, (w.mult : ℝ) * Real.log (1 + ‖x.1 w‖ ^ 2)) +
        2 * ∑ᶠ v : HeightOneSpectrum (𝓞 F), Real.log (max 1 ‖x.2 v‖) ≤
      (2 * ℓ + 4) * ((∑ w ∈ W, Real.log (Λ w)) + ∑ w : InfinitePlace F, (w.mult : ℝ) * Real.log (Λinf w)) +
        (4 * Real.log 2 + 2 * Real.log ℓ) * ∑ w : InfinitePlace F, (w.mult : ℝ) := by sorry
