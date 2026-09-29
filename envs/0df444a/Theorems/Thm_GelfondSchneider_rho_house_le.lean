-- Prove2me | Theorems.Thm_GelfondSchneider_rho_house_le
-- name    : GelfondSchneider.rho_house_le
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-24T20:05:24.669565+00:00
-- url     : https://prove2.me/theorems/62c29048-d0cf-49fc-8309-6427246ebbcf
-- title:
--   House of the first non-zero derivative
-- statement:
--   Let $K$ be a number field, $\alpha', \beta', \gamma' \in K$, $m \ge 1$ and $C_0 \ge 1$. There is $C \ge 1$ such that whenever $n \ge 1$, $q^2 = 2mn$, $n \le r$, $1 \le l_0 \le m$ and the algebraic integers $\eta_{ab}$ have houses at most $C_0^{n} n^{(n+1)/2}$,
--
--   $$\overline{\left|\sum_{a,b} \eta_{ab}\,(a + b\beta')^{r}\,\alpha'^{\,a l_0}\,\gamma'^{\,b l_0}\right|} \le C^{r}\, r^{\,r + 3/2}.$$
-- source:
--   Known: A. O. Gelfond (1934), T. Schneider (1934); this step of Gelfond's proof. Formal proof: Diaz modulus mission, 24 September 2026 (C. Perassi), restructuring the formalization by M. Karatarakis and F. Wiedijk, A formalization of the Gelfond-Schneider theorem, arXiv:2603.24823 (2026), mathlib4 fork at commit cb781672 (Apache 2.0).

import Mathlib

open NumberField

namespace GelfondSchneider

theorem rho_house_le (K : Type*) [Field K] [NumberField K] (α' β' γ' : K) (m : ℕ) (hm : 0 < m)
    (C₀ : ℝ) (hC₀ : 1 ≤ C₀) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (n q r l₀ : ℕ) (η : Fin q → Fin q → 𝓞 K),
      0 < n → q ^ 2 = 2 * m * n → n ≤ r → 1 ≤ l₀ → l₀ ≤ m →
      (∀ a b, house (η a b : K) ≤ C₀ ^ n * (n : ℝ) ^ (((n : ℝ) + 1) / 2)) →
      house (∑ a : Fin q, ∑ b : Fin q, (η a b : K) *
          (((a : ℕ) + 1 : K) + ((b : ℕ) + 1 : K) * β') ^ r *
          α' ^ (((a : ℕ) + 1) * l₀) * γ' ^ (((b : ℕ) + 1) * l₀)) ≤
        C ^ r * (r : ℝ) ^ ((r : ℝ) + 3 / 2) := by
  sorry

end GelfondSchneider
