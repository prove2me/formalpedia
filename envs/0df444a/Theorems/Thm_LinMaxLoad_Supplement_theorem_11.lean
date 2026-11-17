-- Prove2me | Theorems.Thm_LinMaxLoad_Supplement_theorem_11
-- name    : LinMaxLoad.Supplement.theorem_11
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T08:23:26.653978+00:00
-- url     : https://prove2.me/theorems/a5dd938e-8b18-455c-b27b-63f42b9411e9
-- title:
--   Theorem 11 — sets with $\sigma(S) \le 4K$ and $m(S) \ge K-1$ (polynomial dependence on $\sigma$ is necessary)
-- statement:
--   There is an absolute constant $c > 0$ with the following property. Let $p$ be a prime. For every sufficiently large integer $\ell$ (the threshold may depend on $p$), with $n := p^\ell$: for every power $K = p^j$ of $p$ with
--
--   $$
--   2 \le K \le \frac{c \log n}{\log\log n}
--   $$
--
--   and every $u \ge \ell + \log_p K$, there exists a set $S \subseteq \mathbb F_p^u$ of size $n$ such that
--
--   $$
--   \sigma(S) \le 4K \qquad\text{and}\qquad m(S) \ge K - 1 .
--   $$
--
--   Together with Theorem 10 this shows that $m(S)$ is polynomially related to the doubling ratio $\sigma(S)$ in both directions: small doubling alone cannot force $m(S)$ below roughly $\sigma(S)/4$.
--
--   Differences from the source:
--   - reading: “let $\ell \ge 0$ be sufficiently large … there exists an absolute constant $c > 0$” → $\exists c > 0$ first, then $\forall p$, $\exists \ell_0$, $\forall \ell \ge \ell_0$; reason: “absolute” means $c$ is independent of $p$ and $\ell$; the threshold for “sufficiently large” may depend on $p$ (the theorem fixes $p$ first)
--   - reading: $\log$ (base unspecified) → natural logarithm `Real.log`; reason: a different base only rescales the absolute constant $c$ and the threshold
--   - encoding: $K$ a power of $p$, $\log_p K$; $\mathbb F_p^u$; $m(S)$ → $K = p^j$, $\log_p K = j$; `Fin u → ZMod p`; published `linMaxLoad` (its $\lceil\log_p |S|\rceil$ equals $\ell$ since $|S| = p^\ell$); reason: Lean convention; same instances
-- source:
--   Kumar–Zuckerman, Linear Max Load and Additive Structure, STOC 2027 submission (manuscript sha256 9dfdbfff…163b056d), Theorem 11, p.11

import Mathlib
import Definitions.Def_LinMaxLoad_linMaxLoad
import Definitions.Def_LinMaxLoad_Supplement_doublingRatio

namespace LinMaxLoad.Supplement

open LinMaxLoad

/-- **Theorem 11** (p.11) of
Kumar–Zuckerman, *Linear Max Load and Additive Structure*, STOC 2027 submission manuscript
(sha256 9dfdbfffae232e07951f18360ca77987748ff477822893e9f447422f163b056d)).
Let `p` be a prime, and let `ℓ ≥ 0` be a sufficiently large integer. Set `n := p^ℓ`. There
exists an absolute constant `c > 0` such that for any power `K` of `p` satisfying
`2 ≤ K ≤ c log n / log log n` and any `u ≥ ℓ + log_p K`, there exists `S ⊆ F_p^u` of size `n`
such that `σ(S) ≤ 4K` and `m(S) ≥ K − 1`.

**Formalization Note** The absolute constant `c > 0` is chosen first, before `p`; the threshold
`ℓ₀` beyond which `ℓ` is "sufficiently large" may depend on `p` (and `c`). `K = p^j`, so
`log_p K = j`. `log` is the natural logarithm (another base only rescales `c`). `m(S)` is the
published `linMaxLoad`, whose `ℓ = ⌈log_p |S|⌉` equals the theorem's `ℓ` because `|S| = p^ℓ`. -/
theorem theorem_11 :
    ∃ c : ℝ, 0 < c ∧ ∀ (p : ℕ) [Fact p.Prime], ∃ ℓ₀ : ℕ, ∀ ℓ : ℕ, ℓ₀ ≤ ℓ →
      ∀ j : ℕ, (2 : ℝ) ≤ (p : ℝ) ^ j →
        (p : ℝ) ^ j ≤ c * Real.log ((p : ℝ) ^ ℓ) / Real.log (Real.log ((p : ℝ) ^ ℓ)) →
        ∀ u : ℕ, ℓ + j ≤ u →
          ∃ S : Finset (Fin u → ZMod p), S.card = p ^ ℓ ∧
            doublingRatio S ≤ 4 * (p : ℝ) ^ j ∧ (p : ℝ) ^ j - 1 ≤ linMaxLoad p u S := by sorry

end LinMaxLoad.Supplement
