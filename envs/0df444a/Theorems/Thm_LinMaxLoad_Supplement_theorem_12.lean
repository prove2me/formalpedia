-- Prove2me | Theorems.Thm_LinMaxLoad_Supplement_theorem_12
-- name    : LinMaxLoad.Supplement.theorem_12
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T08:23:56.789173+00:00
-- url     : https://prove2.me/theorems/e63c158a-669c-445d-90b5-52292962ddd0
-- title:
--   Theorem 12 — $\sigma(S) \le p^4 q(S)^{-2}$
-- statement:
--   Let $p$ be a prime and $S \subseteq \mathbb F_p^u$ a set of cardinality $n$. Then the doubling ratio of $S$ is controlled by its injectivity probability:
--
--   $$
--   \sigma(S) \le p^4\, q(S)^{-2},
--   $$
--
--   where $q(S) = \Pr_h[M(S,h) = 1]$ for a uniformly random linear map $h : \mathbb F_p^u \to \mathbb F_p^{\ell}$, $\ell = \lceil \log_p n \rceil$. Equivalently, $\sigma(S)\, q(S)^2 \le p^4$.
--
--   So if a random linear map is injective on $S$ with constant probability, then $S$ has constant doubling (for fixed $p$). This is the first step towards the classification of Theorems 13 and 14.
--
--   Differences from the source:
--   - encoding: $\sigma(S) \le p^4 q(S)^{-2}$ → $\sigma(S)\cdot q(S)^2 \le p^4$; reason: equal for $q(S) > 0$; for $q(S) = 0$ the printed bound is $+\infty$ (no content) while Lean's $0^{-2} = 0$ would make the literal form false
--   - encoding: $\mathbb F_p^u$; $q(S)$ with $\ell = \lceil\log_p n\rceil$ → `Fin u → ZMod p`; `injProb` with `Nat.clog p S.card`; reason: Lean convention; same instances
-- source:
--   Kumar–Zuckerman, Linear Max Load and Additive Structure, STOC 2027 submission (manuscript sha256 9dfdbfff…163b056d), Theorem 12, p.12

import Mathlib
import Definitions.Def_LinMaxLoad_Supplement_doublingRatio
import Definitions.Def_LinMaxLoad_Supplement_injProb

namespace LinMaxLoad.Supplement

open LinMaxLoad

/-- **Theorem 12** (p.12) of
Kumar–Zuckerman, *Linear Max Load and Additive Structure*, STOC 2027 submission manuscript
(sha256 9dfdbfffae232e07951f18360ca77987748ff477822893e9f447422f163b056d)).
Let `S ⊆ F_p^u` be of cardinality `n`. Then `σ(S) ≤ p⁴ q(S)⁻²`.

**Formalization Note** Stated as `σ(S) · q(S)² ≤ p⁴`: for `q(S) > 0` this is the printed
inequality, and for `q(S) = 0` the printed right side is `+∞` (no content), while Lean's
`0⁻² = 0` would make the literal form false. `q(S)` is `injProb` (`ℓ = ⌈log_p n⌉`), `σ(S)` is
`doublingRatio`; `n` is arbitrary. -/
theorem theorem_12 (p : ℕ) [Fact p.Prime] (u : ℕ) (S : Finset (Fin u → ZMod p)) :
    doublingRatio S * injProb p u S ^ 2 ≤ (p : ℝ) ^ 4 := by sorry

end LinMaxLoad.Supplement
