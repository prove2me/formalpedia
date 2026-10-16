-- Prove2me | Theorems.Thm_OAI_Erdos3_exists_pivot_grid_bounds
-- name    : OAI.Erdos3.exists_pivot_grid_bounds
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-10-16T01:57:11.757909+00:00
-- url     : https://prove2.me/theorems/c5c09ffb-41e9-4ce4-bf45-08249b1231e5
-- title:
--   Pivot root-factor grid averages are at most (1+δ)^(q^l) for pseudorandom weights
-- statement:
--   Let $s$ be a natural number and $\delta, C_0$ real numbers with $\delta > 0$ and $C_0 \ge 1$. Then there exist a natural number $C \ge 2$ and a real number $\xi_0 > 0$ with the following property. For all natural numbers $N, l, q$ with $N \neq 0$ and all reals $p, \xi$ such that $p \ge 2$, $0 < \xi \le \xi_0$, $N$ is odd, $e^{(p+2)^C} \le N$, $l \le s$, $q \ge 1$ and $q \le C_0\,p$; for every $v : \mathrm{Fin}\,l \to \mathbb Z/N$ and every $\mathrm{slope} \in \mathbb Z/N$ such that $\mathrm{slope} - v_j$ is a unit for every $j$; and for every $f : \mathbb Z/N \to \mathbb R$ with $0 \le f(x) \le e^{p}$ for all $x$ satisfying `CyclicNiltestUpperComparison s N ((p+2)^C) (exp(-(p+2)^C)) f (fun _ => 1 + ξ)` (universe level $0$; OpenAI's predicate that for every rational filtered nilmanifold of degree at most $s$ and every unit-interval-valued niltest $T$ of complexity at most $(p+2)^C$, $\mathbb E_x (f(x) - (1+\xi))\,\mathrm{Re}\,T(x) \le e^{-(p+2)^C}$), the following two bounds hold, where $z$ ranges over $\mathrm{Fin}\,l \to \mathrm{Fin}\,q \to \mathbb Z/N$, $u, w$ over $\mathbb Z/N$ and $\beta$ over $\mathrm{Fin}\,l \to \mathrm{Fin}\,q$, and $\sigma_\beta(z) = \sum_{j} (\mathrm{slope} - v_j)\, z_j(\beta_j)$:
--
--   1. $\mathbb E_z\, \mathbb E_w\, $ `pivotRootFactor v slope f z w` $\le (1+\delta)^{q^l}$, where `pivotRootFactor v slope f z w` $= \prod_{\beta} f(w + \sigma_\beta(z))$;
--   2. for every $\mathrm{choice} : (\mathrm{Fin}\,l \to \mathrm{Fin}\,q) \to \mathrm{Bool}$,
--   $$\mathbb E_z\, \mathbb E_u\, \mathbb E_w \prod_{\beta} \bigl[\text{if } \mathrm{choice}(\beta) \text{ then } f(u + \sigma_\beta(z))\, f(w + \sigma_\beta(z)) \text{ else } 1\bigr] \le (1+\delta)^{2 q^l}.$$
--
--   Lean: `OAI.Erdos3.exists_pivot_grid_bounds` in `lean/OAI/Combinatorics/Progressions/Sampling/PivotGridBounds.lean` (OpenAI); the definitions it uses are in the definitions bundles `OAIErdos3B1325` of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Sampling/PivotGridBounds.lean#L65

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B1325

namespace OAI

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem exists_pivot_grid_bounds (s : ℕ) {delta C0 : ℝ} (hdelta : 0 < delta) (hC0 : 1 ≤ C0) :
    ∃ C : ℕ, 2 ≤ C ∧ ∃ xi0 : ℝ, 0 < xi0 ∧
    ∀ {N l q : ℕ} [NeZero N] {p xi : ℝ}, 2 ≤ p → 0 < xi → xi ≤ xi0 →
      Odd N → Real.exp ((p + 2) ^ C) ≤ N → l ≤ s → 1 ≤ q → (q : ℝ) ≤ C0 * p →
      ∀ (v : Fin l → ZMod N) (slope : ZMod N), (∀ j, IsUnit (slope - v j)) →
      ∀ f : ZMod N → ℝ, (∀ x, 0 ≤ f x ∧ f x ≤ Real.exp p) →
      CyclicNiltestUpperComparison.{0} s N ((p + 2) ^ C)
        (Real.exp (-((p + 2) ^ C))) f (fun _ => 1 + xi) →
      (𝔼 z : Fin l → Fin q → ZMod N, 𝔼 w, pivotRootFactor v slope f z w) ≤
        (1 + delta) ^ (q ^ l) ∧
      ∀ choice : (Fin l → Fin q) → Bool,
        (𝔼 z : Fin l → Fin q → ZMod N, 𝔼 u, 𝔼 w, ∏ beta : Fin l → Fin q,
          if choice beta then
            f (u + ∑ j, (slope - v j) * z j (beta j)) *
            f (w + ∑ j, (slope - v j) * z j (beta j)) else 1) ≤
          (1 + delta) ^ (2 * q ^ l) := by
  sorry

end Erdos3
end
end OAI
