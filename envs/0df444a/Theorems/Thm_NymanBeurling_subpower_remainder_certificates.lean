-- Prove2me | Theorems.Thm_NymanBeurling_subpower_remainder_certificates
-- name    : NymanBeurling.subpower_remainder_certificates
-- status  : Open
-- author  : @marozols
-- created : 2026-11-21T01:57:48.934514+00:00
-- url     : https://prove2.me/theorems/28d55614-fcbe-4180-a244-028572cf1883
-- title:
--   Subpower total cost with vanishing head energy for finite Bagchi certificates
-- statement:
--   Let $R_c(m)=1-\sum_{k\ge 0} c_k\{m/(k+2)\}$ for a finitely supported rational vector $c$, and put $P_H(c)=\sum_{m=1}^H |R_c(m)|^2/[m(m+1)]$. Define the rational certificate $C_K(c)=P_K(c)+(1+\sum_k|c_k|)^2/(K+1)$.
--
--   For every pair of natural numbers $J,L$ there are $H\ge L$, a cutoff $K$, and a finite rational vector $c$ such that
--   $$P_H(c)\le \frac{1}{J+1},\qquad C_K(c)^{J+1}\le H+1.$$
--   Each witness can be checked with finite rational arithmetic. The total cost may grow with $H$. The localized zero obstruction shows that these estimates for all $J,L$ would imply the Riemann hypothesis.
-- source:
--   B. Bagchi, On Nyman, Beurling and Baez-Duarte’s Hilbert space reformulation of the Riemann hypothesis, https://arxiv.org/abs/math/0607733 (discrete remainder model). This localization splits the Mellin pairing at a prescribed integer.

import Mathlib

theorem NymanBeurling.subpower_remainder_certificates (J L : ℕ) :
  ∃ (H K : ℕ) (c : ℕ→₀ℚ), L≤H ∧ (
    let R := fun n : ℕ => 1-∑ k∈c.support,c k*((((n+1)%(k+2):ℕ):ℚ)/(k+2:ℚ))
    let E := fun n : ℕ => ((R n)^2/((n+1:ℚ)*(n+2:ℚ)):ℚ)
    let C : ℚ := (∑ n∈Finset.range K,E n)+(1+∑ k∈c.support,|c k|)^2/(K+1:ℚ)
    (∑ n∈Finset.range H,E n)≤1/(J+1:ℚ) ∧ C^(J+1)≤(H+1:ℚ)) := by sorry
