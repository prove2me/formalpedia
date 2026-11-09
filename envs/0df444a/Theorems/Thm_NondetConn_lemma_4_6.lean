-- Prove2me | Theorems.Thm_NondetConn_lemma_4_6
-- name    : NondetConn.lemma_4_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T06:27:49.626233+00:00
-- url     : https://prove2.me/theorems/7f406ed0-c8b9-46bc-bc02-e915656b505e
-- title:
--   Lemma 4.6 — $\mathbb E_u\mathbb E_a \log(|\mathcal W_{(u,b^{-1}(a(u)))}(b)|+1) \le \log n - \mathbb H(A)/(2n) + O(\log\log n)$
-- statement:
--   There is a constant $K$ such that the following holds. Let $n \ge 2$, $N = 2n$, let $\mathcal A$ be a nonempty set of permutations of $[n]$ and $b$ a permutation of $[n]$ with $\mathsf{bConn}_N(a,b) = 1$ for every $a \in \mathcal A$, and let $A$ be uniform on $\mathcal A$, so that $\mathbb H(A) = \log_2|\mathcal A|$. Then
--   $$
--   \mathop{\mathbb E}_{u\sim[n]}\ \mathop{\mathbb E}_{a\sim A} \log_2\bigl(|\mathcal W_{(u,\,b^{-1}(a(u)))}(b)| + 1\bigr) \le \log_2 n - \frac{\mathbb H(A)}{2n} + K\log_2\log_2 n ,
--   $$
--   where $u$ is uniform on $[n]$ and $\mathcal W$ is taken with respect to $\mathcal A$.
--
--   If the cycle $b^{-1}a$ is close to random, few triples have a fixed cyclic order, and the sets $\mathcal W$ are small; this lemma quantifies that, and it is the last ingredient of the recurrence of Lemma 4.3.
--
--   Differences from the source:
--   - generalization: b ∈ ℬ for the maximizing rectangle 𝒜 × ℬ of S_n with |𝒜| ≥ |ℬ| → any nonempty 𝒜 and any b with bConn n a b for all a ∈ 𝒜 (ℬ dropped); reason: the statement and its proof involve only 𝒜 and b, and use only 𝒜 × {b} ⊆ bConn_N⁻¹(1); the paper's setting is an instance
--   - encoding: E_{u∼[n]} E_{a∼A}, H(A) for A uniform on 𝒜 → (1/n) Σ_u (1/|𝒜|) Σ_{a∈𝒜}, Real.logb 2 |𝒜|; reason: uniform averages and the entropy of a uniform variable; same values
--   - encoding: O(log log n) (n > 1 implicit) → ∃ K, ∀ n ≥ 2, K · log₂ log₂ n, K uniform in n, 𝒜 and b; reason: for n ≥ 3, log₂log₂n ≥ 0.66 absorbs any finitely many n and additive constants; at n = 2 the inequality holds with no error term (|𝒜| ≤ 1, 𝒲 = ∅, LHS 0 ≤ 1 = RHS)
--   - encoding: [n], b⁻¹a, n = N/2 → Fin n (0-based), b⁻¹ * a (apply a first), bConn n; reason: Lean conventions; same instances
-- source:
--   Zhang, Settling Nondeterministic Communication Complexity of Graph Connectivity, arXiv:2610.32346 (held version, sha256 1d4f00d1…4e7ac), Lemma 4.6, p.12 (PDF p.14)

import Mathlib
import Definitions.Def_NondetConn_bConn
import Definitions.Def_NondetConn_W

namespace NondetConn

/-- **Lemma 4.6** (Zhang, *Settling Nondeterministic Communication Complexity of Graph Connectivity*, arXiv:2610.32346 (held version, sha256 1d4f00d1…4e7ac), §4.1, p.12).
There is a constant `K` such that for every `n ≥ 2`, every nonempty set `𝒜` of permutations of
`[n]` and every permutation `b` with `bConn_N(a, b)` for all `a ∈ 𝒜` (`N = 2n`), with `A`
uniform on `𝒜`,
`E_{u∼[n]} E_{a∼A} log(|𝒲_(u, b⁻¹(a(u)))(b)| + 1) ≤ log n − H(A)/(2n) + K log log n`.

**Formalization Note** The expectations are uniform averages, `H(A) = log₂ |𝒜|` for `A` uniform
on `𝒜`, logarithms are base 2, and `O(log log n)` is `K · log₂ log₂ n` with `K` uniform in
`n ≥ 2`, `𝒜` and `b` (at `n = 2` the inequality holds with no error term). The paper's `b ∈ ℬ`
for a maximizing rectangle `𝒜 × ℬ` is replaced by any `b` with `𝒜 × {b}` 1-monochromatic. -/
theorem lemma_4_6 : ∃ K : ℝ, ∀ n : ℕ, 2 ≤ n → ∀ (𝒜 : Finset (Equiv.Perm (Fin n))), 𝒜.Nonempty →
    ∀ b : Equiv.Perm (Fin n), (∀ a ∈ 𝒜, bConn n a b) →
      (1 / (n : ℝ)) * ∑ u : Fin n, ((1 / (𝒜.card : ℝ)) *
          ∑ a ∈ 𝒜, Real.logb 2 (((W 𝒜 b u (b⁻¹ (a u))).card : ℝ) + 1))
        ≤ Real.logb 2 n - Real.logb 2 (𝒜.card : ℝ) / (2 * n)
          + K * Real.logb 2 (Real.logb 2 n) := by sorry

end NondetConn
