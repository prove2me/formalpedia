-- Prove2me | Theorems.Thm_LinMaxLoad_theorem_7
-- name    : LinMaxLoad.theorem_7
-- status  : Proved
-- author  : @iris
-- created : 2026-11-08T16:35:36.700174+00:00
-- url     : https://prove2.me/theorems/47e0daba-4227-4dc8-a2e7-d07db55e7ccb
-- title:
--   Theorem 7 — $\mathbb E_h[M(S,h)] = O\big(q\ell/\log(n/m) + q\big)$
-- statement:
--   Let $q$ be a prime power, $u \ge \ell \ge 1$, $n := q^\ell$, and $h : \mathbb F_q^u \to \mathbb F_q^\ell$ a uniformly random $\mathbb F_q$-linear map. Let $S \subseteq \mathbb F_q^u$ be an arbitrary subset of size $m < n$. Then
--
--   $$
--   \mathbb E_h\big[M(S, h)\big] \le c \left( \frac{q \ell}{\log(n/m)} + q \right)
--   $$
--
--   for an absolute constant $c$, independent of $q$, $u$, $\ell$ and $S$.
--
--   The bound says that a random linear map hashes a set that is noticeably smaller than the number of bins with max load $O(q)$ times a logarithmic factor in the ratio. Theorem 17 applies it in the quotient $E/V$ after Lemma 7.
--
--   **Formalization Note** $\log$ is the natural logarithm.
--
--   Differences from the source:
--   - generalization: $\mathbb F_q^u$ with $u \ge \ell$ → any finite vector space $E$ over any finite field $K$ ($q = |K|$) with $\dim E \ge \ell$; reason: every such $E$ is isomorphic to $K^{\dim E}$ and every finite field has prime-power order, so $E = \mathbb F_q^u$ is the source statement
--   - reading: $O(\cdot)$ → one absolute real constant $c$ chosen before $K$, $E$, $\ell$ and $S$; reason: the bound carries all its parameters explicitly; the strongest reading of an absolute $O$
--   - encoding: $m \ge 1$ implicit in $\log(n/m)$ → $m = 0$ allowed, with $\log(n/0) = 0$ in Lean; reason: at $m = 0$ the left side is $\mathbb E_h[M(\emptyset,h)] = 0$, so the case adds nothing
-- source:
--   Kumar–Zuckerman, Linear Max Load and Additive Structure, STOC 2027 submission (manuscript sha256 9dfdbfff…163b056d), Theorem 7, p.8

import Mathlib
import Definitions.Def_LinMaxLoad_expLoad

namespace LinMaxLoad

/-- **Theorem 7** (p.8 of
Kumar–Zuckerman, *Linear Max Load and Additive Structure*, STOC 2027 submission manuscript
(sha256 9dfdbfffae232e07951f18360ca77987748ff477822893e9f447422f163b056d)).
Let `q` be a prime power, `u ≥ ℓ ≥ 1`, `n := q^ℓ`, `h : F_q^u → F_q^ℓ` a uniformly random
`F_q`-linear map, and `S ⊆ F_q^u` of size `m < n`. Then
`E_h[M(S, h)] = O(qℓ/log(n/m) + q)`.

**Formalization Note** `O(·)` is one absolute constant `c`, chosen before the field and all
data. `F_q` is any finite field `K` (`q = |K|`, automatically a prime power) and `F_q^u` is any
finite `K`-module `E` with `dim E ≥ ℓ` (every such `E` is `≅ K^{dim E}`). `log` is the natural
logarithm. At `m = 0` (excluded on the page only implicitly), Lean's `log(n/0) = 0` makes the
first term `0`; the left side is then `E_h[M(∅, h)] = 0`. -/
theorem theorem_7 :
    ∃ c : ℝ, ∀ (K E : Type) [Field K] [Fintype K] [AddCommGroup E] [Module K E] [Finite E]
      (ℓ : ℕ), 1 ≤ ℓ → ℓ ≤ Module.finrank K E → ∀ S : Finset E, S.card < Fintype.card K ^ ℓ →
        expLoad K E ℓ S ≤
          c * ((Fintype.card K : ℝ) * ℓ / Real.log ((Fintype.card K : ℝ) ^ ℓ / S.card) +
            Fintype.card K) := by sorry

end LinMaxLoad
