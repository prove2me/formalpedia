-- Prove2me | Theorems.Thm_GuthMaynard_abs_card_box_mul_sub_mod_le_of_ne_zero
-- name    : GuthMaynard.abs_card_box_mul_sub_mod_le_of_ne_zero
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-15T21:20:48.032087+00:00
-- url     : https://prove2.me/theorems/f926d5b0-25b9-4095-93cf-deecc994dd52
-- title:
--   Lattice points on a modular hyperbola in a box — any nonzero residue, with a power-saving error
-- statement:
--   There is an absolute constant $C > 0$ with the following property. Let $n, \ell \ge 1$ be natural numbers, let $h \ne 0$ be an integer, and let $p, q \ge 0$ be natural numbers. Let $N$ be the number of pairs $(a, b)$ with $1 \le a \le p$, $1 \le b \le q$ and $\ell ab \equiv h \pmod n$, and let $\rho$ be the number of pairs $(x, y)$ of residues modulo $n$ with $\ell xy \equiv h \pmod n$. Then
--   $$\Big|N - \frac{\rho}{n^2}\,pq\Big| \le C\,\tau(|h|)^2\,|h|\,\big(\tau(n)(1 + \log n)\big)^3\,n^{3/4}\Big(1 + \frac{p + q}{n}\Big),$$
--   where $\tau$ is the number of divisors.
--
--   The main term is the expected one: $\rho/n^2$ is the density of solutions. The error saves a power of $n$ over the trivial bound when the box has sides of size about $n$. The residue $h$ need not be coprime to $n$; the price is the factor $\tau(|h|)^2|h|$.
--
--   **Formalization note.**
--   - This is an auxiliary step, not a claim of any cited paper. It is used in a proof of the twisted fourth moment bound `GuthMaynard.maynard_pratt_twisted_fourth_moment`, which Maynard and Pratt apply in the proof of their Lemma 24 (J. Maynard and K. Pratt, *Half-isolated zeros and zero-density estimates*, Int. Math. Res. Not. IMRN 2024, no. 19, 12978–13014, https://doi.org/10.1093/imrn/rnae191). There it counts the solutions of $\ell_1 ab - \ell_2 cd = h$.
--   - The case of a residue coprime to the modulus is `ArtinPrimitiveRoots.abs_card_box_mul_sub_mod_le`, which rests on a bound for Kloosterman sums.
--   - The pairs $(x, y)$ counted by $\rho$ are taken with $0 \le x, y < n$.
-- source:
--   Maynard, J. and Pratt, K., Half-isolated zeros and zero-density estimates, Int. Math. Res. Not. IMRN 2024, no. 19, 12978–13014, https://doi.org/10.1093/imrn/rnae191 (arXiv:2206.11729v2, whose page numbers are used), p. 38, an auxiliary step (a lattice point count on a modular hyperbola) of a proof of the twisted fourth moment bound in the proof of Lemma 24

import Mathlib

namespace GuthMaynard

theorem abs_card_box_mul_sub_mod_le_of_ne_zero :
    ∃ C : ℝ, 0 < C ∧ ∀ (n ℓ : ℕ) (h : ℤ) (p q : ℕ), 1 ≤ n → 1 ≤ ℓ → h ≠ 0 →
      |(((Finset.Icc 1 p ×ˢ Finset.Icc 1 q).filter
          (fun z : ℕ × ℕ => (n : ℤ) ∣ (ℓ : ℤ) * z.1 * z.2 - h)).card : ℝ) -
        (((Finset.range n ×ˢ Finset.range n).filter
          (fun z : ℕ × ℕ => (n : ℤ) ∣ (ℓ : ℤ) * z.1 * z.2 - h)).card : ℝ) / (n : ℝ) ^ 2 * p * q| ≤
      C * ((h.natAbs.divisors.card : ℝ) ^ 2 * |(h : ℝ)| *
          ((n.divisors.card : ℝ) * (1 + Real.log n)) ^ 3 * (n : ℝ) ^ (3 / 4 : ℝ)) *
        (1 + ((p : ℝ) + q) / n) := by
  sorry

end GuthMaynard
