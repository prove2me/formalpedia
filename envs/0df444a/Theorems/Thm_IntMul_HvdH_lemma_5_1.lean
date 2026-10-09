-- Prove2me | Theorems.Thm_IntMul_HvdH_lemma_5_1
-- name    : IntMul.HvdH.lemma_5_1
-- status  : Open
-- author  : @avi
-- created : 2026-10-08T17:35:52.172015+00:00
-- url     : https://prove2.me/theorems/ed990a51-f316-4d67-8ca3-87bd3a54a099
-- title:
--   Lemma 5.1 — at least $\eta x/(2\log x)$ primes in $((1-2\eta)x,(1-\eta)x]$
-- statement:
--   Let $\eta$ be a real number with $0<\eta<\tfrac14$, and let $x$ be a real number with $x\ge e^{2/\eta}$. Then the interval $\big((1-2\eta)x,(1-\eta)x\big]$ contains many primes:
--   $$\#\{q\text{ prime}:(1-2\eta)x<q\le(1-\eta)x\}\ \ge\ \frac{\eta x}{2\log x}.$$
--
--   Here $\log$ is the natural logarithm. In the paper this lemma supplies $d$ distinct primes $s_1,\dots,s_d$ slightly below the power-of-two lengths $t_1,\dots,t_d$, so that every ratio $t_i/s_i$ stays away from $1$ while the product $t_1\cdots t_d/(s_1\cdots s_d)$ stays bounded.
-- source:
--   D. Harvey, J. van der Hoeven, Integer multiplication in time O(n log n), Annals of Mathematics 193(2) (2021) 563-617, https://doi.org/10.4007/annals.2021.193.2.4 (preprint https://hal.science/hal-02070778v2), §5.2, Lemma 5.1, p. 37

import Mathlib

namespace IntMul.HvdH

theorem lemma_5_1 (η : ℝ) (hη₀ : 0 < η) (hη₁ : η < 1 / 4) (x : ℝ) (hx : Real.exp (2 / η) ≤ x) :
    η * x / (2 * Real.log x) ≤
      ({q : ℕ | q.Prime ∧ (1 - 2 * η) * x < q ∧ (q : ℝ) ≤ (1 - η) * x}.ncard : ℝ) := by sorry

end IntMul.HvdH
