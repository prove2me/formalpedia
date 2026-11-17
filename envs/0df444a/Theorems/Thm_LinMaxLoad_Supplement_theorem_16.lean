-- Prove2me | Theorems.Thm_LinMaxLoad_Supplement_theorem_16
-- name    : LinMaxLoad.Supplement.theorem_16
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T08:26:22.707206+00:00
-- url     : https://prove2.me/theorems/ff51573c-863c-4529-9974-e83bf6abc0d6
-- title:
--   Theorem 16 — $q_k(S) \ge \delta$: $(1-\varepsilon)n$ points of $S$ covered by $(p^{k^2}/(\delta\varepsilon^k))^{O(p^3)}$ affine spaces
-- statement:
--   There is an absolute constant $c > 0$ such that the following holds. Let $p$ be a prime and $S \subseteq \mathbb F_p^u$ a set of size $n$. Assume $q_k(S) \ge \delta$ for some integer $k \ge 1$ and $0 < \delta \le 1$. Then for every $0 < \varepsilon < 1$ one can cover at least $(1-\varepsilon)n$ points of $S$ with at most
--
--   $$
--   \left(\frac{p^{k^2}}{\delta\, \varepsilon^k}\right)^{c\, p^3}
--   $$
--
--   affine spaces, each of size at most $n$. Here $q_k(S) = \Pr_h[M(S,h) \le k]$ for a uniformly random linear map $h : \mathbb F_p^u \to \mathbb F_p^\ell$, $\ell = \lceil \log_p n \rceil$, and an affine space is a coset $x + W$ of a subspace $W \le \mathbb F_p^u$.
--
--   Hence, for $p, k = O(1)$ and $\delta = \Omega(1)$, all but an $\varepsilon$-fraction of a set with bounded linear max load lies in $(1/\varepsilon)^{O(1)}$ affine spaces of size $n$.
--
--   Differences from the source:
--   - reading: $(\cdot)^{O(p^3)}$ → $(\cdot)^{c\,p^3}$ with one absolute $c > 0$ chosen before $p, u, k, \delta, \varepsilon, S$; reason: the strongest reading of an absolute $O$; the base is $\ge 1$, so the bound is monotone in $c$
--   - encoding: “cover $(1-\varepsilon)n$ points in $S$ with $N$ affine spaces of size at most $n$” → points $x_i$ and subspaces $W_i$ ($i < N$) with $|W_i| \le n$ and at least $(1-\varepsilon)n$ points of $S$ in $\bigcup_i (x_i + W_i)$, $N$ at most the real bound; reason: same meaning
--   - encoding: $\mathbb F_p^u$; $q_k(S)$ with $\ell = \lceil\log_p n\rceil$ → `Fin u → ZMod p`; `loadProb` with `Nat.clog p S.card`; reason: Lean convention; same instances
-- source:
--   Kumar–Zuckerman, Linear Max Load and Additive Structure, STOC 2027 submission (manuscript sha256 9dfdbfff…163b056d), Theorem 16, p.18 (introduction form Theorem 4, p.5)

import Mathlib
import Definitions.Def_LinMaxLoad_Supplement_loadProb

namespace LinMaxLoad.Supplement

open LinMaxLoad

open Classical in
/-- **Theorem 16** (p.18) of
Kumar–Zuckerman, *Linear Max Load and Additive Structure*, STOC 2027 submission manuscript
(sha256 9dfdbfffae232e07951f18360ca77987748ff477822893e9f447422f163b056d)).
Let `S ⊆ F_p^u` be a set of size `n`. Assume `q_k(S) ≥ δ` for some integer `k ≥ 1` and
`0 < δ ≤ 1`. For every `0 < ε < 1`, one can cover `(1 − ε)n` points in `S` with
`(p^{k²}/(δ ε^k))^{O(p³)}` affine spaces of size at most `n`.

**Formalization Note** `(·)^{O(p³)}` is read as `(·)^{c p³}` with one absolute constant `c > 0`
chosen before `p, u, k, δ, ε, S`. An affine space is `x + W` for a point `x` and a subspace
`W`, encoded by the pair `(x_i, W_i)`; "of size at most `n`" is `|W_i| ≤ n`; "cover `(1 − ε)n`
points in `S`" means at least `(1 − ε)n` points of `S` lie in `⋃_i (x_i + W_i)`. `q_k(S)` is
`loadProb` (`ℓ = ⌈log_p n⌉`); `n` is arbitrary. The number `N` of affine spaces is a natural
number at most the real bound. -/
theorem theorem_16 :
    ∃ c : ℝ, 0 < c ∧ ∀ (p : ℕ) [Fact p.Prime] (u k : ℕ) (δ ε : ℝ)
      (S : Finset (Fin u → ZMod p)), 1 ≤ k → 0 < δ → δ ≤ 1 → δ ≤ loadProb p u k S →
      0 < ε → ε < 1 →
        ∃ (N : ℕ) (x : Fin N → Fin u → ZMod p) (W : Fin N → Submodule (ZMod p) (Fin u → ZMod p)),
          (N : ℝ) ≤ ((p : ℝ) ^ (k ^ 2) / (δ * ε ^ k)) ^ (c * (p : ℝ) ^ 3) ∧
          (∀ i, Nat.card (W i) ≤ S.card) ∧
          (1 - ε) * (S.card : ℝ) ≤ ((S.filter fun s => ∃ i, s - x i ∈ W i).card : ℝ) := by sorry

end LinMaxLoad.Supplement
