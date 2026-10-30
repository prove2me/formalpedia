-- Prove2me | Theorems.Thm_KUMultimodular_multimodular_correct_and_cost
-- name    : KUMultimodular.multimodular_correct_and_cost
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-30T00:01:41.029636+00:00
-- url     : https://prove2.me/theorems/b122ed9c-f101-40af-a847-8a9b271dd036
-- title:
--   Theorem 4.2: correctness and bit complexity of MULTIMODULAR (corrected: $\max 2$ in $\ell$, $m \ge 1$, clipped logs)
-- statement:
--   Fix the number of rounds $t \ge 1$. There are constants $C_1, C_2 > 0$ and $c \in \mathbb N$ (depending on $t$) such that the following holds. Let $r \ge 1$, $m \ge 1$, $d, N \in \mathbb N$, let $f \in (\mathbb Z/r\mathbb Z)[X_0,\dots,X_{m-1}]$ have degree at most $d-1$ in each variable, and let $\alpha_0,\dots,\alpha_{N-1} \in (\mathbb Z/r\mathbb Z)^m$. Then Algorithm MULTIMODULAR with $t$ rounds returns $f(\alpha_i)$ for every $i$, and it uses at most
--   $$C_1\,\bigl(\lambda_t(d)^m + N\bigr)\,\lambda_t(\log r)\,\lambda_t(d)^t\,\lambda_t(m)^{m+t+1}\cdot\bigl(C_2 \log^{(t)} r\bigr)^m\cdot\bigl(\lg(m\,d\,\lg r)\bigr)^c$$
--   bit operations, where $\lambda_t$ and the iterated logarithm $\log^{(t)}$ are those of `KUMultimodular.lam` (base 2, clipped below at $1$).
--
--   For $m \le d^{o(1)}$ and suitable $t$ this is $(d^m + N)^{1+o(1)} \log^{1+o(1)} r$, nearly linear in the input size (Corollary 4.3), in every characteristic.
--
--   **Formalization Note** The algorithm is `multimodular t r m d N c α`; its cost is the `cost` field of the same computation whose `val` is the output, in the model `KUMultimodular.Timed`.
--
--   Differences from the source:
--   - correction: ℓ = 16 log(d^m (r−1)^{md}) in Step 2 → ℓ = ⌊16 ln max(2, d^m (r−1)^{md})⌋ (ellValue); reason: counterexample: r = 2, m = d = 1, f = 1, α_0 = 0, t = 1: the printed ℓ is 16 log 1 = 0, there are no primes, Step 5 returns 0 ≠ 1 = f(α_0); for d^m(r−1)^{md} ≥ 2 the two ℓ agree
--   - correction: all m (including m = 0) → 1 ≤ m; reason: counterexample: r = 10000, m = 0, d = 1, f = 9999, N = 1: d^m(r−1)^{md} = 1, so ℓ ≤ 11 and p_1⋯p_k ≤ 2310 < 9999, and the algorithm returns 9999 mod 2310 = 759 ≠ 9999 (with the printed ℓ = 0 it returns 0); also the printed bound contains λ_t(m)^{m+t+1} = λ_t(0)^{t+1} = 0
--   - correction: λ_t and log^{(t)} unclipped → λ_t(x) with argument max(1, x) and every logarithm lg x = max(1, log₂ x); lg in the poly log factor; reason: counterexample: t = 2, d = 1, m = 1: the printed bound contains λ_2(d)^t = λ_2(1)^2 = (1 · log 1)^2 = 0, while the algorithm performs at least one bit operation; λ_1(0) = 0 for d = 0 likewise
--   - reading: O(·)·O(log^{(t)} r)^m·poly log(md log r), t arbitrary → ∀ t ≥ 1, ∃ C₁ C₂ > 0 and c ∈ ℕ (C₂ inside the m-th power); reason: the constants may depend on t (uniformly in t the bound is false: for m = d = 2 every level has at least 8 primes, so the cost is at least 8^t, while the clipped bound for fixed r grows like 4^t); O(·)^m is read with the constant inside the power, as printed
--   - reading: bit operations (Theorems 4.1, 4.2, 4.4) → the bit-cost model KUMultimodular.Timed: linear charges for reading, traversal, addition and table look-up; each cited subroutine (fast integer/polynomial arithmetic, sieve, remainder tree, Chinese remaindering, fast univariate multipoint evaluation, radix conversion) returns its exact result and is charged S(⌊log₂ S⌋+1)⁴ on data of total bit size S; reason: the paper counts bit operations and charges each step the cited cost of a standard subroutine (proof of Theorem 4.2, p. 13); every charge is at least that cited cost up to a constant, so the model never under-charges
--   - reading: log (base not stated) → natural logarithm in ℓ; base-2 logarithms in the running-time bound; reason: ℓ uses the reading of Lemma 2.4; the base of the logarithms in an O-bound only changes constants
--   - encoding: r arbitrary; f and the points given by their lifts → 0 < r; coefficient table (Fin m → Fin d) → ZMod r, output Fin N → ZMod r; reason: ZMod 0 = ℤ is not a ring ℤ/rℤ with finitely many residues; same instances otherwise
-- source:
--   Kedlaya, Umans, Fast polynomial factorization and modular composition, Dagstuhl Seminar Proceedings 08381 (2008), Theorem 4.2, p. 13 (Algorithm MULTIMODULAR, p. 12)

import Mathlib
import Definitions.Def_KUMultimodular_Timed
import Definitions.Def_KUMultimodular_lam
import Definitions.Def_KUMultimodular_densePoly
import Definitions.Def_KUMultimodular_multimodular

namespace KUMultimodular

/-- **Theorem 4.2** (Kedlaya–Umans, Dagstuhl Seminar Proceedings 08381 (2008), p. 13). For every
number of rounds `t ≥ 1` there are constants `C₁, C₂ > 0` and `c` such that for every `r ≥ 1`,
`m ≥ 1`, `d`, `N`, every `f ∈ (ℤ/rℤ)[X_0, …, X_{m-1}]` with degree at most `d - 1` in each variable
and all points `α_0, …, α_{N-1} ∈ (ℤ/rℤ)^m`, Algorithm MULTIMODULAR returns `f(α_i)` for every `i`
and uses at most
`C₁ (λ_t(d)^m + N) λ_t(log r) λ_t(d)^t λ_t(m)^{m+t+1} · (C₂ log^{(t)} r)^m · (log (m d log r))^c`
bit operations (logarithms base 2, clipped below at `1`). -/
theorem multimodular_correct_and_cost (t : ℕ) (ht : 1 ≤ t) :
    ∃ (C₁ C₂ : ℝ) (c : ℕ), 0 < C₁ ∧ 0 < C₂ ∧
      ∀ (r : ℕ), 0 < r → ∀ (m d N : ℕ) (c₀ : (Fin m → Fin d) → ZMod r)
        (α : Fin N → Fin m → ZMod r), 1 ≤ m →
        (∀ i, (multimodular t r m d N c₀ α).val i = MvPolynomial.eval (α i) (densePoly c₀)) ∧
        ((multimodular t r m d N c₀ α).cost : ℝ) ≤
          C₁ * ((lam t d) ^ m + N) * lam t (Real.logb 2 r) * (lam t d) ^ t
            * (lam t m) ^ (m + t + 1) * (C₂ * ilog t r) ^ m * (lg (m * d * lg r)) ^ c := by sorry

end KUMultimodular
