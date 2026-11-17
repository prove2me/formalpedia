-- Prove2me | Theorems.Thm_LinMaxLoad_Supplement_theorem_10
-- name    : LinMaxLoad.Supplement.theorem_10
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T08:22:47.925715+00:00
-- url     : https://prove2.me/theorems/a113945c-8e24-4380-89ed-d3cc163df478
-- title:
--   Theorem 10 — $m(S) \le 1 - 1/n + \sigma(S)^2$
-- statement:
--   Let $p$ be a prime and $S \subseteq \mathbb F_p^u$ a set of size $n$. Then the expected linear max load of $S$ is bounded by its doubling ratio:
--
--   $$
--   m(S) \le 1 - \frac1n + \sigma(S)^2 .
--   $$
--
--   Here $m(S) = \mathbb E_h[M(S,h)]$ for a uniformly random linear map $h : \mathbb F_p^u \to \mathbb F_p^\ell$ with $\ell = \lceil \log_p n \rceil$, and $\sigma(S) = |S+S|/|S|$.
--
--   The bound shows that sets of bounded doubling have bounded expected linear max load, and it is tight for subspaces, where $m(S) = 2 - 1/n$ (Lemma 4).
--
--   Differences from the source:
--   - encoding: $\mathbb F_p^u$; $m(S)$ with $\ell = \lceil\log_p |S|\rceil$ → `Fin u → ZMod p`; published `linMaxLoad` with `Nat.clog p S.card`; reason: Lean convention; same instances
--   - encoding: $S$ of size $n$ (implicitly $n \ge 1$) → every finite $S$, including $S = \emptyset$; reason: at $S=\emptyset$ Lean reads $1/0 = 0$, $\sigma(\emptyset)=0$, $m(\emptyset)=0$, and the claim $0 \le 1$ is true; no nonempty instance changes
-- source:
--   Kumar–Zuckerman, Linear Max Load and Additive Structure, STOC 2027 submission (manuscript sha256 9dfdbfff…163b056d), Theorem 10, p.10

import Mathlib
import Definitions.Def_LinMaxLoad_linMaxLoad
import Definitions.Def_LinMaxLoad_Supplement_doublingRatio

namespace LinMaxLoad.Supplement

open LinMaxLoad

/-- **Theorem 10** (p.10) of
Kumar–Zuckerman, *Linear Max Load and Additive Structure*, STOC 2027 submission manuscript
(sha256 9dfdbfffae232e07951f18360ca77987748ff477822893e9f447422f163b056d)).
Let `S ⊂ F_p^u` be a set of size `n`. Then `m(S) ≤ 1 − 1/n + σ(S)²`.

**Formalization Note** `m(S)` is the published `linMaxLoad` (`ℓ = ⌈log_p n⌉`, `h` uniform over
all linear maps `F_p^u → F_p^ℓ`); `σ(S) = |S + S|/|S|` is `doublingRatio`. The statement is
for every finite `S`; at `S = ∅` Lean reads `1/0 = 0` and `σ(∅) = 0`, and the claim
`0 ≤ 1` holds. -/
theorem theorem_10 (p : ℕ) [Fact p.Prime] (u : ℕ) (S : Finset (Fin u → ZMod p)) :
    linMaxLoad p u S ≤ 1 - 1 / (S.card : ℝ) + doublingRatio S ^ 2 := by sorry

end LinMaxLoad.Supplement
