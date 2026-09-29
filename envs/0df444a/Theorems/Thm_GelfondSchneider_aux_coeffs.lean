-- Prove2me | Theorems.Thm_GelfondSchneider_aux_coeffs
-- name    : GelfondSchneider.aux_coeffs
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-24T20:05:27.986157+00:00
-- url     : https://prove2.me/theorems/58990e61-4127-41a3-b61f-f9254333c532
-- title:
--   Gelfond's auxiliary function: small integral coefficients by Siegel's lemma
-- statement:
--   Let $K$ be a number field, $\alpha', \beta', \gamma' \in K$ with $\alpha', \gamma' \ne 0$, and $m \ge 1$. There is a constant $C \ge 1$ such that for all $n \ge 1$ and $q$ with $q^2 = 2mn$ there are algebraic integers $\eta_{ab} \in \mathcal O_K$ ($1 \le a, b \le q$), not all zero, with houses at most $C^{n} n^{(n+1)/2}$, such that
--
--   $$\sum_{a,b} \eta_{ab}\,(a + b\beta')^{k}\,\alpha'^{\,aj}\,\gamma'^{\,bj} = 0 \qquad (1 \le j \le m,\ 0 \le k < n).$$
--
--   There are $q^2 = 2mn$ unknowns and $mn$ equations, so Siegel's lemma over $\mathcal O_K$ applies with exponent one; the system's entries are bounded by `GelfondSchneider.system_entry_house_le` after clearing denominators.
-- source:
--   Known: A. O. Gelfond (1934), T. Schneider (1934); this step of Gelfond's proof. Formal proof: Diaz modulus mission, 24 September 2026 (C. Perassi), restructuring the formalization by M. Karatarakis and F. Wiedijk, A formalization of the Gelfond-Schneider theorem, arXiv:2603.24823 (2026), mathlib4 fork at commit cb781672 (Apache 2.0).

import Mathlib

open NumberField

namespace GelfondSchneider

theorem aux_coeffs (K : Type*) [Field K] [NumberField K] (α' β' γ' : K)
    (hα' : α' ≠ 0) (hγ' : γ' ≠ 0) (m : ℕ) (hm : 0 < m) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ n q : ℕ, 0 < n → q ^ 2 = 2 * m * n →
      ∃ η : Fin q → Fin q → 𝓞 K, η ≠ 0 ∧
        (∀ a b, house (η a b : K) ≤ C ^ n * (n : ℝ) ^ (((n : ℝ) + 1) / 2)) ∧
        ∀ j : ℕ, 1 ≤ j → j ≤ m → ∀ k < n, ∑ a : Fin q, ∑ b : Fin q,
          (η a b : K) * (((a : ℕ) + 1 : K) + ((b : ℕ) + 1 : K) * β') ^ k *
            α' ^ (((a : ℕ) + 1) * j) * γ' ^ (((b : ℕ) + 1) * j) = 0 := by
  sorry

end GelfondSchneider
