-- Prove2me | Theorems.Thm_KUMultimodular_fpEval_correct_and_cost
-- name    : KUMultimodular.fpEval_correct_and_cost
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-29T23:59:47.766994+00:00
-- url     : https://prove2.me/theorems/15906bff-9ac9-4bb8-8bc6-6c54001ffe27
-- title:
--   Theorem 4.1: multipoint evaluation over $\mathbb F_p$ in $O(m(d^m+p^m+N)\,\mathrm{poly}\log p)$ (corrected: $m \ge 1$)
-- statement:
--   There are constants $C > 0$ and $c \in \mathbb N$ such that the following holds. Let $p$ be a prime, $m \ge 1$, $d, N \in \mathbb N$, let $f \in \mathbb F_p[X_0,\dots,X_{m-1}]$ have degree at most $d-1$ in each variable (given by its dense coefficient table), and let $\alpha_0,\dots,\alpha_{N-1} \in \mathbb F_p^m$. Then the algorithm of the proof of Theorem 4.1 outputs $f(\alpha_i)$ for every $i = 0,\dots,N-1$, and it uses at most
--   $$C\, m\,\bigl(d^m + p^m + N\bigr)\,(\log_2 p)^c$$
--   bit operations.
--
--   This is the base case of the multimodular algorithm: its running time is nearly linear in the input size $d^m + mN$ only when $p$ is small, and Algorithm MULTIMODULAR reduces to that case.
--
--   **Formalization Note** The algorithm is `fpEval` and its cost is the `cost` field of the same computation whose `val` is the output, in the model `KUMultimodular.Timed`.
--
--   Differences from the source:
--   - correction: all m (including m = 0) → 1 ≤ m; reason: for m = 0 the printed bound O(m(d^m + p^m + N) poly(log p)) is 0, while any algorithm reads its input and writes N ≥ 1 outputs: p = 2, m = 0, d = 1, N = 1 needs at least one bit operation
--   - reading: there exists a deterministic algorithm → the statement for the algorithm of the proof (fpEval); reason: the theorem is proved by exhibiting that algorithm; the statement about it implies the existence statement
--   - reading: bit operations (Theorems 4.1, 4.2, 4.4) → the bit-cost model KUMultimodular.Timed: linear charges for reading, traversal, addition and table look-up; each cited subroutine (fast integer/polynomial arithmetic, sieve, remainder tree, Chinese remaindering, fast univariate multipoint evaluation, radix conversion) returns its exact result and is charged S(⌊log₂ S⌋+1)⁴ on data of total bit size S; reason: the paper counts bit operations and charges each step the cited cost of a standard subroutine (proof of Theorem 4.2, p. 13); every charge is at least that cited cost up to a constant, so the model never under-charges
--   - encoding: O(·) and poly(log p) → explicit constants C > 0 and c ∈ ℕ, uniform in p, m, d, N; log base 2 clipped at 1 (lg p = log₂ p for p ≥ 2); reason: the meaning of the asymptotic notation; for primes the clipping changes nothing
--   - encoding: f given by its list of coefficients; outputs f(α_0), …, f(α_{N-1}) → coefficient table (Fin m → Fin d) → ZMod p, output Fin N → ZMod p; reason: Lean convention; same instances (degree at most d − 1 in each variable)
-- source:
--   Kedlaya, Umans, Fast polynomial factorization and modular composition, Dagstuhl Seminar Proceedings 08381 (2008), Theorem 4.1 and its proof, pp. 11–12

import Mathlib
import Definitions.Def_KUMultimodular_Timed
import Definitions.Def_KUMultimodular_lam
import Definitions.Def_KUMultimodular_densePoly
import Definitions.Def_KUMultimodular_fpEval

namespace KUMultimodular

/-- **Theorem 4.1** (Kedlaya–Umans, Dagstuhl Seminar Proceedings 08381 (2008), p. 11), for the
algorithm of its proof (`fpEval`). There are constants `C > 0` and `c` such that for every prime
`p`, all `m ≥ 1`, `d`, `N`, every `f ∈ 𝔽_p[X_0, …, X_{m-1}]` with degree at most `d - 1` in each
variable (coefficient table `c₀`) and all points `α_0, …, α_{N-1} ∈ 𝔽_p^m`, the algorithm outputs
`f(α_i)` for every `i` and uses at most `C · m · (d^m + p^m + N) · (log₂ p)^c` bit operations. -/
theorem fpEval_correct_and_cost :
    ∃ (C : ℝ) (c : ℕ), 0 < C ∧
      ∀ (p : ℕ), p.Prime → ∀ (m d N : ℕ) (c₀ : (Fin m → Fin d) → ZMod p)
        (α : Fin N → Fin m → ZMod p), 1 ≤ m →
        (∀ i, (fpEval p m d N c₀ α).val i = MvPolynomial.eval (α i) (densePoly c₀)) ∧
        ((fpEval p m d N c₀ α).cost : ℝ) ≤
          C * m * ((d : ℝ) ^ m + (p : ℝ) ^ m + N) * (lg p) ^ c := by sorry

end KUMultimodular
