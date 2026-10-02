-- Prove2me | Theorems.Thm_GelfondSchneider_deriv_upper
-- name    : GelfondSchneider.deriv_upper
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-24T20:05:27.335743+00:00
-- url     : https://prove2.me/theorems/d74690db-d2c0-4b78-81b2-800698673390
-- title:
--   Analytic upper bound for the first non-zero derivative of Gelfond's auxiliary function
-- statement:
--   Let $l, \beta \in \mathbb C$, $m \ge 1$ and $C_0 \ge 1$. There is $C \ge 1$ such that the following holds. Let $n \ge 1$, $q^2 = 2mn$, $n \le r$ and $1 \le l_0 \le m$. Let $E(z) = \sum_{a,b} c_{ab}\, e^{(a + b\beta) l z}$ with $|c_{ab}| \le C_0^{n} n^{(n+1)/2}$, and suppose all derivatives of order below $r$ vanish at $1, \dots, m$. Then
--
--   $$|E^{(r)}(l_0)| \le C^{r}\, r^{\,r(3-m)/2 + 3/2}.$$
--
--   The proof applies the grid estimate `Transcendence.expPoly_grid_estimate` to $F(z) = E(z + 1)$ on the one-dimensional grid $\{0, \dots, m - 1\}$, with vanishing order $r$, at the point $l_0 - 1$ and with $u = 2 + r/q$. The zeros at all of $1, \dots, m$, including $l_0$ itself, give the factor $(u - 1)^{-mr}$, and $1/(u - 1) \le q/r \le \sqrt{2m}\, r^{-1/2}$ turns it into $r^{-rm/2}$ up to a factor $C^{r}$.
-- source:
--   Known: A. O. Gelfond (1934), T. Schneider (1934); this step of Gelfond's proof. Formal proof: Diaz modulus mission, 24 September 2026 (C. Perassi), restructuring the formalization by M. Karatarakis and F. Wiedijk, A formalization of the Gelfond-Schneider theorem, arXiv:2603.24823 (2026), mathlib4 fork at commit cb781672 (Apache 2.0).

import Mathlib

open NumberField

namespace GelfondSchneider

theorem deriv_upper (l β : ℂ) (m : ℕ) (hm : 0 < m) (C₀ : ℝ) (hC₀ : 1 ≤ C₀) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (n q r l₀ : ℕ) (c : Fin q → Fin q → ℂ),
      0 < n → q ^ 2 = 2 * m * n → n ≤ r → 1 ≤ l₀ → l₀ ≤ m →
      (∀ a b, ‖c a b‖ ≤ C₀ ^ n * (n : ℝ) ^ (((n : ℝ) + 1) / 2)) →
      (∀ j : ℕ, 1 ≤ j → j ≤ m → ∀ k < r, iteratedDeriv k (fun z : ℂ => ∑ a : Fin q, ∑ b : Fin q,
          c a b * Complex.exp ((((a : ℕ) + 1 : ℂ) + ((b : ℕ) + 1 : ℂ) * β) * l * z)) (j : ℂ) = 0) →
      ‖iteratedDeriv r (fun z : ℂ => ∑ a : Fin q, ∑ b : Fin q,
          c a b * Complex.exp ((((a : ℕ) + 1 : ℂ) + ((b : ℕ) + 1 : ℂ) * β) * l * z)) (l₀ : ℂ)‖ ≤
        C ^ r * (r : ℝ) ^ ((r : ℝ) * (3 - m) / 2 + 3 / 2) := by
  sorry

end GelfondSchneider
