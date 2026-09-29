-- Prove2me | Theorems.Thm_GelfondSchneider_rho_denominator
-- name    : GelfondSchneider.rho_denominator
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-24T20:05:15.092309+00:00
-- url     : https://prove2.me/theorems/cd68ef56-23e3-4b24-9858-0f3a3818c994
-- title:
--   A common denominator for the first non-zero derivative
-- statement:
--   Let $K$ be a number field, $\alpha', \beta', \gamma' \in K$ and $m \in \mathbb N$. There is a non-zero integer $D$ such that for all $n$, $q$, $r$, $l_0$ with $n \ge 1$, $q^2 = 2mn$, $n \le r$ and $1 \le l_0 \le m$, and all $\eta_{ab} \in \mathcal O_K$,
--
--   $$D^{r} \sum_{a,b} \eta_{ab}\,(a + b\beta')^{r}\,\alpha'^{\,a l_0}\,\gamma'^{\,b l_0}$$
--
--   is an algebraic integer. The exponent of the denominator grows linearly in $r$ because $q \le q^2 = 2mn \le 2mr$.
-- source:
--   Known: A. O. Gelfond (1934), T. Schneider (1934); this step of Gelfond's proof. Formal proof: Diaz modulus mission, 24 September 2026 (C. Perassi), restructuring the formalization by M. Karatarakis and F. Wiedijk, A formalization of the Gelfond-Schneider theorem, arXiv:2603.24823 (2026), mathlib4 fork at commit cb781672 (Apache 2.0).

import Mathlib

open NumberField

namespace GelfondSchneider

theorem rho_denominator (K : Type*) [Field K] [NumberField K] (α' β' γ' : K)
    (m : ℕ) :
    ∃ D : ℤ, D ≠ 0 ∧ ∀ (n q r l₀ : ℕ) (η : Fin q → Fin q → 𝓞 K),
      0 < n → q ^ 2 = 2 * m * n → n ≤ r → 1 ≤ l₀ → l₀ ≤ m →
      IsIntegral ℤ ((D : K) ^ r * ∑ a : Fin q, ∑ b : Fin q, (η a b : K) *
          (((a : ℕ) + 1 : K) + ((b : ℕ) + 1 : K) * β') ^ r *
          α' ^ (((a : ℕ) + 1) * l₀) * γ' ^ (((b : ℕ) + 1) * l₀)) := by
  sorry

end GelfondSchneider
