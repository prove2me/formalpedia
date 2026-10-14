-- Prove2me | Theorems.Thm_IntMul_HvdH_thm_4_1
-- name    : IntMul.HvdH.thm_4_1
-- status  : Proved
-- author  : @xuanji
-- created : 2026-10-11T20:40:29.330379+00:00
-- url     : https://prove2.me/theorems/e2988667-9ead-48c9-a123-ffa41a0c9548
-- title:
--   HvdH Thm 4.1: $\mathcal F_{\mathbf s}=2^{2d\alpha^2}\mathcal B\mathcal F_{\mathbf t}\mathcal A$ (multidimensional Gaussian resampling)
-- statement:
--   **Multidimensional Gaussian resampling** (Harvey–van der Hoeven, Theorem 4.1).
--
--   Let $d\ge1$, let $s_1,\dots,s_d$ and $t_1,\dots,t_d$ be positive integers with $s_i<t_i$ and $\gcd(s_i,t_i)=1$, and let $\alpha\ge2$ be an integer with $\alpha^2\,(t_i/s_i-1)\ge1$ for every $i$. For $\mathbf s=(s_1,\dots,s_d)$ write $\mathcal F_{\mathbf s}$ for the normalised $d$-dimensional DFT on $\mathbb C^{s_1}\otimes\cdots\otimes\mathbb C^{s_d}$ (functions on $\prod_i\mathbb Z/s_i$):
--   $$(\mathcal F_{\mathbf s}u)_k=\frac{1}{s_1\cdots s_d}\sum_{j}\prod_{i=1}^d e^{-2\pi i\, j_ik_i/s_i}\;u_j .$$
--   Then there are linear maps $\mathcal A$ and $\mathcal B$, both of norm at most $1$ for the sup norm, with
--   $$\mathcal F_{\mathbf s}=2^{2d\alpha^2}\,\mathcal B\,\mathcal F_{\mathbf t}\,\mathcal A .$$
--
--   So a DFT of awkward (for example prime) dimensions is reduced, at the cost of $O(d\alpha^2)$ bits of precision, to a DFT of convenient dimensions $t_i$ (powers of two in the paper). This is the step that lets the algorithm of Harvey–van der Hoeven use the synthetic FFT in Section 5.
--
--   *Formalization note.* $\mathcal A=\bigotimes_i\mathcal A_i$ and $\mathcal B=\bigotimes_i\mathcal B_i$ are tensor products of the one-dimensional maps of `IntMul.HvdH.prop_4_7_i`.
-- source:
--   Harvey, van der Hoeven, Integer multiplication in time O(n log n), Annals of Math. 193 (2021), https://hal.science/hal-02070778, Section 4.1, Theorem 4.1 (alpha taken integral, constant 2^{2 d alpha^2})

import Mathlib

namespace IntMul.HvdH
theorem thm_4_1 {d : ℕ} (s t : Fin d → ℕ) [∀ i, NeZero (s i)]
    [∀ i, NeZero (t i)] (α : ℕ)
    (hst : ∀ i, s i < t i) (hcop : ∀ i, Nat.Coprime (s i) (t i)) (hα : 2 ≤ α)
    (hθ : ∀ i, 1 ≤ (α : ℝ) ^ 2 * ((t i : ℝ) / s i - 1)) :
    ∃ (A : (((i : Fin d) → ZMod (s i)) → ℂ) →L[ℂ] (((i : Fin d) → ZMod (t i)) → ℂ))
      (B : (((i : Fin d) → ZMod (t i)) → ℂ) →L[ℂ] (((i : Fin d) → ZMod (s i)) → ℂ)),
      ‖A‖ ≤ 1 ∧ ‖B‖ ≤ 1 ∧
      ∀ u k, (∏ i, (s i : ℂ))⁻¹ * ∑ j, (∏ i, (ZMod.stdAddChar (-(j i * k i)) : ℂ)) * u j =
        (2 : ℂ) ^ (2 * d * α ^ 2) * B (fun k' => (∏ i, (t i : ℂ))⁻¹ *
          ∑ l, (∏ i, (ZMod.stdAddChar (-(l i * k' i)) : ℂ)) * A u l) k := by sorry
end IntMul.HvdH
