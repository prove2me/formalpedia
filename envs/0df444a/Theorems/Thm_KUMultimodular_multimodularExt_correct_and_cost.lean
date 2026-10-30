-- Prove2me | Theorems.Thm_KUMultimodular_multimodularExt_correct_and_cost
-- name    : KUMultimodular.multimodularExt_correct_and_cost
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-30T00:04:39.935381+00:00
-- url     : https://prove2.me/theorems/1d2d249b-fab8-4433-9987-21af43516471
-- title:
--   Theorem 4.4: correctness and bit complexity of MULTIMODULAR-FOR-EXTENSION-RING (corrected: $\max 2$ in $\ell$, $m \ge 1$, clipped logs)
-- statement:
--   Fix the number of rounds $t \ge 1$. There are constants $C_1, C_2 > 0$ and $c \in \mathbb N$ (depending on $t$) such that the following holds. Let $r \ge 1$, let $E \in (\mathbb Z/r\mathbb Z)[Z]$ be monic of degree $e$, so that $R = (\mathbb Z/r\mathbb Z)[Z]/(E(Z))$ is a finite ring of cardinality $q = r^e$. Let $m \ge 1$, $d, N \in \mathbb N$, let $f \in R[X_0,\dots,X_{m-1}]$ have degree at most $d-1$ in each variable, and let $\alpha_0,\dots,\alpha_{N-1} \in R^m$. Then Algorithm MULTIMODULAR-FOR-EXTENSION-RING with $t$ rounds returns $f(\alpha_i)$ for every $i = 0,\dots,N-1$, and it uses at most
--   $$C_1\,\bigl(\lambda_t(d)^m + N\bigr)\,\lambda_t(\log q)\,\lambda_t(d)^{t+2}\,\lambda_t(m)^{m+t+3}\cdot\Bigl(C_2\,\log^{(t-1)}\bigl(d^2m^2\,\lg q\,\lg\lg q\bigr)\Bigr)^m\cdot\bigl(\lg(m\,d\,\lg q)\bigr)^c$$
--   bit operations, where $\lambda_t$, $\lg$ and $\log^{(t-1)}$ are those of `KUMultimodular.lam` (base 2, clipped below at $1$; the argument of $\log^{(t-1)}$ is clipped at $1$ too).
--
--   This is the paper's algorithm for multivariate multipoint evaluation over every finite field and every ring $(\mathbb Z/r\mathbb Z)[Z]/(E(Z))$: for $m \le d^{o(1)}$ its running time is $(d^m + N)^{1+o(1)} \log^{1+o(1)} q$ (Corollary 4.5). Through the reduction of Section 3 it gives modular composition, and then polynomial factorization over $\mathbb F_q$, in nearly linear time.
--
--   **Formalization Note** $R$ is `AdjoinRoot E` with `hE : E.Monic`, $e$ is `E.natDegree` and $q = r^e$ as a real number. The algorithm is `multimodularExt t E hE coef α`; its cost is the `cost` field of the same computation whose `val` is the output, in the model `KUMultimodular.Timed`.
--
--   Differences from the source:
--   - correction: all m (including m = 0) → 1 ≤ m; reason: counterexample: R = 𝔽_2[Z]/(Z² + Z + 1), m = 0, d = 1, f = Z, N = 1: M = 3, r' = 3, Step 2 maps Z to 3 mod 3 = 0, and the algorithm returns 0 ≠ Z = f(α_0)
--   - correction: ℓ = 16 log(d^m (r−1)^{md}) in Step 2 of MULTIMODULAR → ℓ = ⌊16 ln max(2, d^m (r−1)^{md})⌋ (ellValue); reason: counterexample: R = ℤ/2ℤ (E = Z, e = 1), m = d = 1, f = 1, α_0 = 0, t = 1: M = 2, r' = 2, MULTIMODULAR over ℤ/2ℤ has the printed ℓ = 16 log 1 = 0, no primes, β_0 = 0, and the algorithm returns 0 ≠ 1
--   - correction: λ_t and log^{(t−1)} unclipped → λ_t(x) with argument max(1, x), every logarithm lg x = max(1, log₂ x), and max(1, ·) on the argument of log^{(t−1)}; reason: counterexample: t = 2, d = 1, m = 1: the printed bound contains λ_2(d)^{t+2} = λ_2(1)^4 = 0, while the algorithm performs at least one bit operation
--   - reading: O(·)·O(log^{(t−1)}(…))^m·poly log(md log q), t arbitrary → ∀ t ≥ 1, ∃ C₁ C₂ > 0 and c ∈ ℕ (C₂ inside the m-th power); reason: the constants may depend on t (uniformly in t the bound fails already for Theorem 4.2: at least 8^t against 4^t for m = d = 2); O(·)^m is read with the constant inside the power, as printed
--   - reading: bit operations (Theorems 4.1, 4.2, 4.4) → the bit-cost model KUMultimodular.Timed: linear charges for reading, traversal, addition and table look-up; each cited subroutine (fast integer/polynomial arithmetic, sieve, remainder tree, Chinese remaindering, fast univariate multipoint evaluation, radix conversion) returns its exact result and is charged S(⌊log₂ S⌋+1)⁴ on data of total bit size S; reason: the paper counts bit operations and charges each step the cited cost of a standard subroutine (proof of Theorem 4.2, p. 13); every charge is at least that cited cost up to a constant, so the model never under-charges
--   - reading: log (base not stated) → natural logarithm in ℓ; base-2 logarithms in the running-time bound; reason: ℓ uses the reading of Lemma 2.4; the base of the logarithms in an O-bound only changes constants
--   - encoding: R = (ℤ/rℤ)[Z]/(E(Z)) of cardinality q; f and the points as coefficient lists → AdjoinRoot E over ZMod r with 0 < r, q = r^{natDegree E}; coefficient table (Fin m → Fin d) → AdjoinRoot E, output Fin N → AdjoinRoot E; reason: ZMod 0 = ℤ does not give a finite ring; the cardinality of AdjoinRoot E is r^e; same instances otherwise
-- source:
--   Kedlaya, Umans, Fast polynomial factorization and modular composition, Dagstuhl Seminar Proceedings 08381 (2008), Theorem 4.4, p. 15 (Algorithm MULTIMODULAR-FOR-EXTENSION-RING, p. 15; Algorithm MULTIMODULAR, p. 12)

import Mathlib
import Definitions.Def_KUMultimodular_Timed
import Definitions.Def_KUMultimodular_lam
import Definitions.Def_KUMultimodular_densePoly
import Definitions.Def_KUMultimodular_multimodularExt

namespace KUMultimodular

/-- **Theorem 4.4** (Kedlaya–Umans, Dagstuhl Seminar Proceedings 08381 (2008), p. 15). For every
number of rounds `t ≥ 1` there are constants `C₁, C₂ > 0` and `c` such that for every `r ≥ 1`,
every monic `E ∈ (ℤ/rℤ)[Z]` (so `R = (ℤ/rℤ)[Z]/(E(Z))` has cardinality `q = r^{deg E}`), all
`m ≥ 1`, `d`, `N`, every `f ∈ R[X_0, …, X_{m-1}]` with degree at most `d - 1` in each variable and
all points `α_0, …, α_{N-1} ∈ R^m`, Algorithm MULTIMODULAR-FOR-EXTENSION-RING returns `f(α_i)` for
every `i` and uses at most
`C₁ (λ_t(d)^m + N) λ_t(log q) λ_t(d)^{t+2} λ_t(m)^{m+t+3}
  · (C₂ log^{(t-1)}(d^2 m^2 log q log log q))^m · (log (m d log q))^c`
bit operations (logarithms base 2, clipped below at `1`). -/
theorem multimodularExt_correct_and_cost (t : ℕ) (ht : 1 ≤ t) :
    ∃ (C₁ C₂ : ℝ) (c : ℕ), 0 < C₁ ∧ 0 < C₂ ∧
      ∀ (r : ℕ), 0 < r → ∀ (E : Polynomial (ZMod r)) (hE : E.Monic) (m d N : ℕ)
        (coef : (Fin m → Fin d) → AdjoinRoot E) (α : Fin N → Fin m → AdjoinRoot E), 1 ≤ m →
        (∀ i, (multimodularExt t E hE coef α).val i = MvPolynomial.eval (α i) (densePoly coef)) ∧
        ((multimodularExt t E hE coef α).cost : ℝ) ≤
          C₁ * ((lam t d) ^ m + N) * lam t (Real.logb 2 ((r : ℝ) ^ E.natDegree))
            * (lam t d) ^ (t + 2) * (lam t m) ^ (m + t + 3)
            * (C₂ * ilog (t - 1) (max 1 ((d : ℝ) ^ 2 * (m : ℝ) ^ 2 * lg ((r : ℝ) ^ E.natDegree)
                * lg (lg ((r : ℝ) ^ E.natDegree))))) ^ m
            * (lg (m * d * lg ((r : ℝ) ^ E.natDegree))) ^ c := by sorry

end KUMultimodular
