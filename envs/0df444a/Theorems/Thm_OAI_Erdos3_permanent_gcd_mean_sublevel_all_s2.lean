-- Prove2me | Theorems.Thm_OAI_Erdos3_permanent_gcd_mean_sublevel_all_s2
-- name    : OAI.Erdos3.permanent_gcd_mean_sublevel_all_s2
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-17T10:28:20.963764+00:00
-- url     : https://prove2.me/theorems/4cdd146c-a570-4447-982c-3e746ca22394
-- title:
--   The mean of gcd(permanent, p^a)/p^a over random n×n matrices modulo p^a is at most (n+1) p^(-a/2^n)
-- statement:
--   Let $n$ and $a$ be natural numbers with $a > 0$, and let $p$ be a prime. Let $x$ be a uniformly random $n \times n$ matrix with entries in $\mathbb{Z}/p^a\mathbb{Z}$, and let $\operatorname{per}(x) \in \mathbb{Z}/p^a\mathbb{Z}$ be its permanent; write $v(x) \in \{0, 1, \dots, p^a - 1\}$ for the canonical representative of $\operatorname{per}(x)$. Then
--   $$\mathbb{E}_x\, \frac{\gcd\bigl(v(x),\, p^a\bigr)}{p^a} \;\le\; (n+1)\, p^{-a/2^n},$$
--   where the exponent $-a/2^n$ is a real exponent. (For $v(x) = 0$, $\gcd(0, p^a) = p^a$.)
--
--   Lean: `OAI.Erdos3.permanent_gcd_mean_sublevel_all_s2`, which states OpenAI's `OAI.Erdos3.permanent_gcd_mean_sublevel_all` (in `lean/OAI/Combinatorics/Progressions/Polynomial/PolynomialDifferencePermanentBlocks.lean`); the definitions it uses are in the definitions bundles  of version 2 of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Polynomial/PolynomialDifferencePermanentBlocks.lean (declaration OAI.Erdos3.permanent_gcd_mean_sublevel_all)

import Mathlib
import Definitions.Def_ErdosReciprocal

section

namespace OAI

section

namespace Erdos3
open scoped BigOperators Classical

theorem permanent_gcd_mean_sublevel_all_s2 {n p a : ℕ} [NeZero p]
    (hp : p.Prime) (ha : 0 < a) :
    (𝔼 x : (Fin n × Fin n) → ZMod (p ^ a),
      ((Matrix.permanent (fun i j => x (i, j))).val.gcd (p ^ a) : ℝ) / (p ^ a : ℕ)) ≤
        ((n + 1 : ℕ) : ℝ) * (p : ℝ) ^ (-(a : ℝ) / (2 : ℝ) ^ n) := by
  sorry

end Erdos3

end

end OAI
end
