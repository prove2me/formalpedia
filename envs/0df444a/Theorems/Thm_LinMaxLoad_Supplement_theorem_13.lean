-- Prove2me | Theorems.Thm_LinMaxLoad_Supplement_theorem_13
-- name    : LinMaxLoad.Supplement.theorem_13
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T08:24:31.533544+00:00
-- url     : https://prove2.me/theorems/788b3a89-b73b-41e5-a8db-372d43254350
-- title:
--   Theorem 13 — $q(S) \ge \delta$ forces $S = S + V$ with $|V| \ge p^{-p^{\tilde O(p^8\delta^{-8})}} n$
-- statement:
--   There is an absolute constant $c > 0$ such that the following holds. Let $p$ be a prime, $u \ge \ell \ge 1$ integers, and $S \subseteq \mathbb F_p^u$ a set of size $n := p^\ell$. Write $X := p^8 \delta^{-8}$ and $B := c\, X (\log X)^c$ (this is the $\tilde O(p^8\delta^{-8})$ of the paper). If $q(S) \ge \delta > 0$, then there is a subspace $V \le \mathbb F_p^u$ such that
--
--   $$
--   |V| \ge p^{-p^{B}}\, n \qquad\text{and}\qquad S = S + V .
--   $$
--
--   In other words, $S$ is the disjoint union of at most $p^{p^{B}}$ shifts of a subspace: there is a set $T$ of at most $p^{p^B}$ points, lying in pairwise distinct cosets of $V$, with $S = V + T$.
--
--   Here $q(S) = \Pr_h[M(S,h) = 1]$ for a uniformly random linear map $h : \mathbb F_p^u \to \mathbb F_p^\ell$. For fixed $p$ and $\delta$ this says that a set of size a power of $p$ that is injectively hashed with constant probability is a union of $O(1)$ cosets of one subspace.
--
--   Differences from the source:
--   - reading: $\tilde O(p^8\delta^{-8})$ → $c\,X(\log X)^c$ with $X = p^8\delta^{-8}$ and one absolute $c > 0$ chosen before $p, u, \ell, \delta, S$; reason: the literal meaning of $\tilde O$ with absolute constants; $X \ge 2^8$ under the hypotheses (as $q(S) \le 1$), so $\log X > 0$
--   - encoding: “$S$ is the disjoint union of at most $N$ shifts of a subspace” → $S = V + T$ with $|T| \le N$ and the points of $T$ in pairwise distinct cosets of $V$; reason: the shifts $t + V$ are then pairwise disjoint; same meaning
--   - encoding: $\mathbb F_p^u$; $S + V$; $q(S)$; $|V|$ → `Fin u → ZMod p`; published `cosetSum V S`; `injProb`; `Nat.card V` with real powers; reason: Lean convention; same instances
-- source:
--   Kumar–Zuckerman, Linear Max Load and Additive Structure, STOC 2027 submission (manuscript sha256 9dfdbfff…163b056d), Theorem 13, p.13

import Mathlib
import Definitions.Def_LinMaxLoad_cosetSum
import Definitions.Def_LinMaxLoad_Supplement_injProb

namespace LinMaxLoad.Supplement

open LinMaxLoad

/-- **Theorem 13** (p.13) of
Kumar–Zuckerman, *Linear Max Load and Additive Structure*, STOC 2027 submission manuscript
(sha256 9dfdbfffae232e07951f18360ca77987748ff477822893e9f447422f163b056d)).
Let `u ≥ ℓ ≥ 1` be integers, and `S ⊆ F_p^u` of size `n := p^ℓ`. If `q(S) ≥ δ > 0`, there exists
a subspace `V ≤ F_p^u` such that `|V| ≥ p^{−p^{Õ(p⁸δ⁻⁸)}} n` and `S = S + V`. In other words, `S`
is the disjoint union of at most `p^{p^{Õ(p⁸δ⁻⁸)}}` shifts of a subspace.

**Formalization Note** `Õ(X)`, `X = p⁸δ⁻⁸`, is read as `c·X·(log X)^c` with one absolute
constant `c > 0` chosen before `p, u, ℓ, δ, S` (`X ≥ 2⁸` whenever the hypotheses hold, since
`q(S) ≤ 1`, so `log X > 0`). `S + V` is the published `cosetSum V S`. The "in other words"
clause is stated as well: `S = V + T` for a set `T` of at most `p^{p^{c X (log X)^c}}` points
lying in pairwise distinct cosets of `V` (so the shifts `t + V`, `t ∈ T`, are disjoint).
`q(S)` is `injProb`; powers are real powers. -/
theorem theorem_13 :
    ∃ c : ℝ, 0 < c ∧ ∀ (p : ℕ) [Fact p.Prime] (u ℓ : ℕ), 1 ≤ ℓ → ℓ ≤ u →
      ∀ (S : Finset (Fin u → ZMod p)), S.card = p ^ ℓ →
      ∀ δ : ℝ, 0 < δ → δ ≤ injProb p u S →
        ∃ V : Submodule (ZMod p) (Fin u → ZMod p),
          (p : ℝ) ^ (-((p : ℝ) ^ (c * ((p : ℝ) ^ 8 / δ ^ 8) *
              Real.log ((p : ℝ) ^ 8 / δ ^ 8) ^ c))) * ((p ^ ℓ : ℕ) : ℝ) ≤ (Nat.card V : ℝ) ∧
          cosetSum V S = S ∧
          ∃ T : Finset (Fin u → ZMod p),
            (T.card : ℝ) ≤ (p : ℝ) ^ ((p : ℝ) ^ (c * ((p : ℝ) ^ 8 / δ ^ 8) *
              Real.log ((p : ℝ) ^ 8 / δ ^ 8) ^ c)) ∧
            cosetSum V T = S ∧
            ∀ t ∈ T, ∀ t' ∈ T, t - t' ∈ V → t = t' := by sorry

end LinMaxLoad.Supplement
