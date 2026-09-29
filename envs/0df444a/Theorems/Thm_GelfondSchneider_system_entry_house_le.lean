-- Prove2me | Theorems.Thm_GelfondSchneider_system_entry_house_le
-- name    : GelfondSchneider.system_entry_house_le
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-24T20:04:43.878033+00:00
-- url     : https://prove2.me/theorems/cbe83e8d-f145-4454-a29e-dcf7bd32ac01
-- title:
--   House of the entries of Gelfond's linear system
-- statement:
--   Let $K$ be a number field, $\alpha', \beta', \gamma' \in K$ and $m \ge 1$. There is a constant $C \ge 1$ such that for all $n \ge 1$ and $q$ with $q^2 = 2mn$, all $1 \le a, b \le q$, all $1 \le j \le m$ and all $k < n$,
--
--   $$\overline{\left|(a + b\beta')^{k}\,\alpha'^{\,aj}\,\gamma'^{\,bj}\right|} \le C^{n}\, n^{(n-1)/2}.$$
--
--   These are the entries of the linear system that Gelfond's auxiliary function must satisfy, before denominators are cleared.
-- source:
--   Known: A. O. Gelfond (1934), T. Schneider (1934); this step of Gelfond's proof. Formal proof: Diaz modulus mission, 24 September 2026 (C. Perassi), restructuring the formalization by M. Karatarakis and F. Wiedijk, A formalization of the Gelfond-Schneider theorem, arXiv:2603.24823 (2026), mathlib4 fork at commit cb781672 (Apache 2.0).

import Mathlib

open NumberField

namespace GelfondSchneider

theorem system_entry_house_le (K : Type*) [Field K] [NumberField K] (α' β' γ' : K)
    (m : ℕ) (hm : 0 < m) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ n q a b j k : ℕ, 0 < n → q ^ 2 = 2 * m * n →
      1 ≤ a → a ≤ q → 1 ≤ b → b ≤ q → 1 ≤ j → j ≤ m → k < n →
      house (((a : K) + (b : K) * β') ^ k * α' ^ (a * j) * γ' ^ (b * j)) ≤
        C ^ n * (n : ℝ) ^ (((n : ℝ) - 1) / 2) := by
  sorry

end GelfondSchneider
